import OAI.Algebra.DepthFive.ParameterBounds
import OAI.Algebra.DepthFive.CircuitWeightBound
import OAI.Algebra.DepthFive.OddDegreeThreshold

namespace OAI

noncomputable section

namespace Problem335.LowerParameters

/-- All hypotheses of the circuit weight estimate hold simultaneously for
the actual integer and analytic parameters beyond one uniform threshold. -/
theorem exists_weightParameters_cutoff :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → WeightParameters n (s n : ℝ) (q n) := by
  obtain ⟨n₁, h₁⟩ := eventually_admissible
  obtain ⟨n₂, h₂⟩ := eventually_odd_degree_smallness
  refine ⟨max (max n₁ n₂) 64, ?_⟩
  intro n hn
  have hn64 : 64 ≤ n := (le_max_right _ _).trans hn
  have hn4 : 4 ≤ n := by omega
  have hn1 : n₁ ≤ n := (le_max_left n₁ n₂).trans ((le_max_left _ _).trans hn)
  have hn2 : n₂ ≤ n := (le_max_right n₁ n₂).trans ((le_max_left _ _).trans hn)
  have hA := h₁ n hn1
  have hq := q_pos hn4
  have henv := hA.q_upper.trans hA.sqrt_upper_power
  refine ⟨hn64, ?_, hA.s_lower, hA.s_upper, hq,
    hA.q_upper.trans hA.sqrt_upper_half, hA.q_upper, henv, ?_⟩
  · exact_mod_cast s_pos hn4
  · exact h₂ n hn2 (q n) hq.le henv

/-- Filter form of the actual-parameter specialization, for final asymptotic assembly. -/
theorem eventually_weightParameters :
    ∀ᶠ n : ℕ in Filter.atTop, WeightParameters n (s n : ℝ) (q n) :=
  Filter.eventually_atTop.mpr exists_weightParameters_cutoff

end Problem335.LowerParameters

end

end OAI
