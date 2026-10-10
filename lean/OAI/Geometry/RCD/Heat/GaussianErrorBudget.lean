import OAI.Geometry.RCD.Heat.GaussianShellKernel

namespace OAI

/-! # Finite normalization ranges and uniform Gaussian tails

Only finitely many outward scales need the small splitting error. Beyond
that range a fixed geometric bound suffices, and its Gaussian tail tends
to zero uniformly as the range grows.
-/

open Filter
open scoped Topology BigOperators

noncomputable section

namespace RegularPointCoordinates

/-- A finite prefix has the small analytic error; only a fixed bound is
used beyond the last controlled scale. -/
def splitSeriesTerm (a : ℕ → ℝ) (ε : ℝ) (N j : ℕ) : ℝ :=
  (if j < N then ε else 1) * a j

theorem summable_splitSeriesTerm {a : ℕ → ℝ} (ha : Summable a) (ε : ℝ) (N : ℕ) :
    Summable (splitSeriesTerm a ε N) := by
  apply (summable_nat_add_iff N).mp
  simpa only [splitSeriesTerm, not_lt.mpr (Nat.le_add_left N _), ite_false, one_mul] using
    (summable_nat_add_iff N).mpr ha

theorem tsum_splitSeriesTerm {a : ℕ → ℝ} (ha : Summable a) (ε : ℝ) (N : ℕ) :
    (∑' j, splitSeriesTerm a ε N j) =
      ε * (∑ j ∈ Finset.range N, a j) + ∑' j, a (j + N) := by
  have he := (summable_splitSeriesTerm ha ε N).sum_add_tsum_nat_add N
  have hp : (∑ j ∈ Finset.range N, splitSeriesTerm a ε N j) =
      ε * (∑ j ∈ Finset.range N, a j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [splitSeriesTerm, Finset.mem_range.mp hj, ite_true]
  have ht : (∑' j, splitSeriesTerm a ε N (j + N)) = ∑' j, a (j + N) := by
    apply tsum_congr
    intro j
    simp only [splitSeriesTerm, not_lt.mpr (Nat.le_add_left N j), ite_false, one_mul]
  rw [hp, ht] at he
  exact he.symm

theorem tsum_splitSeriesTerm_le {a : ℕ → ℝ} (ha : Summable a)
    (hpos : ∀ j, 0 ≤ a j) {ε : ℝ} (hε : 0 ≤ ε) (N : ℕ) :
    (∑' j, splitSeriesTerm a ε N j) ≤ ε * (∑' j, a j) + ∑' j, a (j + N) := by
  rw [tsum_splitSeriesTerm ha ε N]
  have hm := mul_le_mul_of_nonneg_left
    (ha.sum_le_tsum (Finset.range N) (fun j _ => hpos j)) hε
  linarith

/-- Small local errors and a sufficiently remote tail give any prescribed
uniform tolerance. Both choices are made before selecting a scale. -/
theorem exists_small_splitSeriesTerm {a : ℕ → ℝ} (ha : Summable a)
    (hpos : ∀ j, 0 ≤ a j) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ M, N ≤ M → ∀ e, 0 ≤ e → e ≤ ε →
      (∑' j, splitSeriesTerm a e M j) < η := by
  have htotal : 0 ≤ ∑' j, a j := tsum_nonneg hpos
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_sum_nat_add a).eventually_lt_const (half_pos hη))
  let ε := η / (2 * ((∑' j, a j) + 1))
  have hε : 0 < ε := div_pos hη (by positivity)
  refine ⟨N, ε, hε, fun M hM e he heε => ?_⟩
  have hb := tsum_splitSeriesTerm_le ha hpos he M
  have htail := hN M hM
  have hprod : ε * (∑' j, a j) < η / 2 := by
    dsimp [ε]
    have hd : 0 < 2 * ((∑' j, a j) + 1) := by positivity
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hd).mpr
    nlinarith
  have hm := mul_le_mul_of_nonneg_right heε htotal
  linarith

end RegularPointCoordinates

end

end OAI
