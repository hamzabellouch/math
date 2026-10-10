import OAI.Combinatorics.ProgressionColoring.CyclicWitness
import OAI.Combinatorics.ProgressionColoring.UniformTransfer
import OAI.Combinatorics.ProgressionColoring.LargeColorConsequences

namespace OAI

namespace QuantitativeVanDerWaerden

open Filter

/-- An absolute quantitative lower bound, uniform over all color counts. -/
theorem uniform_lower_bound :
    ∃ K : ℕ, ∀ k ≥ K, ∀ r ≥ 2,
      (k : ℝ) ^ ((1 / 100000 : ℝ) * k * (Nat.log 2 r : ℝ)) < (W r k : ℝ) := by
  exact uniform_lower_of_cyclicLowerBound exists_cyclic_coloring

/-- The same bound with the floor of the real base-two logarithm. -/
theorem uniform_lower_bound_floor :
    ∃ K : ℕ, ∀ k ≥ K, ∀ (r : ℕ), r ≥ 2 →
      (k : ℝ) ^ ((1 / 100000 : ℝ) * k *
        (⌊Real.log (r : ℝ) / Real.log 2⌋₊ : ℝ)) < (W r k : ℝ) := by
  obtain ⟨K, hK⟩ := uniform_lower_bound
  refine ⟨K, ?_⟩
  intro k hk r hr
  rw [← natLog_two_eq_floor_log]
  exact hK k hk r hr

/-- The existential-constant formulation, with a single absolute threshold. -/
theorem exists_uniform_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, ∀ k ≥ K, ∀ r ≥ 2,
      (k : ℝ) ^ (c * k * (Nat.log 2 r : ℝ)) < (W r k : ℝ) := by
  exact ⟨1 / 100000, by norm_num, uniform_lower_bound⟩

/-- For each fixed color count at least two, the full kth-root limit diverges. -/
theorem kthRoot_tendsto {r : ℕ} (hr : 2 ≤ r) :
    Tendsto (fun k : ℕ => (W r k : ℝ) ^ (1 / (k : ℝ))) atTop atTop := by
  exact kthRoot_tendsto_of_cyclicLowerBound (c := 1 / 100000)
    (by norm_num) exists_cyclic_coloring hr

/-- The actual infimum over every color count at least two diverges. -/
theorem length_rate_tendsto :
    Tendsto (fun k : ℕ => ⨅ r : {r : ℕ // 2 ≤ r},
      Real.log (W r.val k : ℝ) / ((k : ℝ) * Real.log (r.val : ℝ))) atTop atTop := by
  exact length_rate_tendsto_of_cyclicLowerBound (c := 1 / 100000)
    (by norm_num) exists_cyclic_coloring

end QuantitativeVanDerWaerden

end OAI
