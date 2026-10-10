import OAI.Combinatorics.BalancedRyser.Selection.LineOccupancyConcentration

namespace OAI

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace Balanced.LineOccupancy

universe u

theorem exists_initial_failure_threshold (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      N ≤ Fintype.card F →
      offsetEventProbability (F := F)
        {M | ∃ l, l ∉ initialDeletedLines M ∧
          ((linePoints l ∩ initiallyRetained M).card : ℝ) <
            (Fintype.card F : ℝ) / 5} < ε := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_mean_gap.and (tendsto_line_union_bound.eventually_lt_const hε))
  refine ⟨N, ?_⟩
  intro F _ _ _ hq
  exact (initial_failure_probability_le (hN (Fintype.card F) hq).1).trans_lt
    (hN (Fintype.card F) hq).2

theorem exists_initial_occupancy_error :
    ∃ ε : ℕ → ℝ, (∀ q, 0 ≤ ε q) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        offsetEventProbability (F := F)
          {M | ∃ l, l ∉ initialDeletedLines M ∧
            ((linePoints l ∩ initiallyRetained M).card : ℝ) <
              (Fintype.card F : ℝ) / 5} ≤ ε (Fintype.card F) := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.mp eventually_mean_gap
  let b : ℕ → ℝ := fun q =>
    (q : ℝ) * ((q : ℝ) + 1) * (2 * Real.exp (-(q : ℝ) / 3200))
  let ε : ℕ → ℝ := fun q => if N ≤ q then b q else 1
  have hnonneg : ∀ q, 0 ≤ ε q := by
    intro q
    dsimp [ε, b]
    split_ifs <;> positivity
  have heq : ε =ᶠ[atTop] b := by
    filter_upwards [eventually_ge_atTop N] with q hq
    simp [ε, hq]
  refine ⟨ε, hnonneg, tendsto_line_union_bound.congr' heq.symm, ?_⟩
  intro F _ _ _
  by_cases hq : N ≤ Fintype.card F
  · simpa [ε, b, hq] using initial_failure_probability_le (hN _ hq)
  · let : MeasurableSpace (MergedPairs F) := ⊤
    let : MeasurableSingletonClass (MergedPairs F) := ⟨fun _ => trivial⟩
    simp only [ε, ite_eq_right hq]
    rw [offsetEventProbability_eq_real]
    simp

end Balanced.LineOccupancy

end

end OAI
