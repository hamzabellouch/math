import OAI.Algebra.DepthFive.ActualCircuitRank
import OAI.Algebra.DepthFive.ActualImmRank
import OAI.Algebra.DepthFive.LowerAsymptotics

namespace OAI

/-! Circuit-size lower bounds from eventual rank and second-trace estimates
for the normalized IMM matrix. -/

noncomputable section

namespace Problem335

open LowerParameters

/-- An eventual lower bound for the configured IMM rank, together with the
proved circuit upper bound, gives the exact complex circuit-size conclusion. -/
theorem complex_depth_five_lower_bound_of_eventual_rank_lower (C : ℝ)
    (hlower : ∀ᶠ n : ℕ in Filter.atTop,
      rankDimension n * Real.exp (-C * Real.sqrt (n : ℝ)) ≤
        rankData n (imm ℂ n)) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ c : Depth5Circuit ℂ n,
      circuitValue c = imm ℂ n →
      (n : ℝ) ^ (Real.sqrt (n : ℝ) / 400) ≤ (circuitSize c : ℝ) := by
  obtain ⟨Nlower, hNlower⟩ := Filter.eventually_atTop.mp hlower
  obtain ⟨Nupper, hNupper⟩ := exists_rankData_circuit_upper_cutoff
  obtain ⟨Nnumeric, hNnumeric⟩ :=
    eventual_size_lower_bound_of_rank_bounds C (24 + 4 * Real.log 5)
  refine ⟨max 4 (max Nlower (max Nupper Nnumeric)), ?_⟩
  intro n hn c hc
  have hn4 : 4 ≤ n := (le_max_left _ _).trans hn
  have hnlo : Nlower ≤ n :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnup : Nupper ≤ n :=
    (le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hnnum : Nnumeric ≤ n :=
    (le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  apply hNnumeric n hnnum (circuitSize c) (rankDimension n)
    (rankData n (imm ℂ n)) (Nat.cast_nonneg _) (rankDimension_pos hn4)
    (hNlower n hnlo)
  simpa only [hc] using hNupper n hnup c hc

/-- The second-trace bound, together with the first-trace and circuit
estimates, implies the complex circuit-size lower bound. -/
theorem complex_depth_five_lower_bound_of_eventual_second_trace (C : ℝ)
    (hsecond : ∀ᶠ n : ℕ in Filter.atTop, ∀ hn : 16 ≤ n,
      (((immNormalizedMatrix n
          (balancedLayer (Nat.le_trans (by decide : 4 ≤ 16) hn)) (a n) (b n)).conjTranspose *
        immNormalizedMatrix n
          (balancedLayer (Nat.le_trans (by decide : 4 ≤ 16) hn)) (a n) (b n)) ^ 2).trace.re ≤
        rankDimension n * rankMomentScale n ^ 2 *
          Real.exp (C * Real.sqrt (n : ℝ))) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ c : Depth5Circuit ℂ n,
      circuitValue c = imm ℂ n →
      (n : ℝ) ^ (Real.sqrt (n : ℝ) / 400) ≤ (circuitSize c : ℝ) := by
  apply complex_depth_five_lower_bound_of_eventual_rank_lower (128 + C)
  filter_upwards [hsecond, Filter.eventually_ge_atTop 16] with n hn hlarge
  simpa only [neg_mul] using
    rankData_imm_lower_of_second_trace_bound hlarge C (hn hlarge)

end Problem335

end

end OAI
