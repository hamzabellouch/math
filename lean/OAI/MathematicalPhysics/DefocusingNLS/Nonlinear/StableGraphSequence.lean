import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

namespace OAI

/-! # The weighted sequence space for the nonlinear stable graph

A bounded sequence records `2^n` times the physical perturbation.  Thus the
ambient sequence space is Banach without imposing an auxiliary completeness
assumption on decaying sequences.  These are supporting lemmas for `nl:graph`;
no spectral splitting or nonlinear evolution is assumed here.
-/

open Filter Topology

open scoped BoundedContinuousFunction

namespace DefocusingNLS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual value of a perturbation encoded in the weighted sequence space. -/
noncomputable def stableSequenceValue (x : ℕ →ᵇ E) (n : ℕ) : E :=
  (1 / 2 : ℝ) ^ n • x n

theorem norm_stableSequenceValue_le (x : ℕ →ᵇ E) (n : ℕ) :
    ‖stableSequenceValue x n‖ ≤ (1 / 2 : ℝ) ^ n * ‖x‖ := by
  unfold stableSequenceValue
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (x.norm_coe_le_norm n) (by positivity)

theorem stableSequenceValue_tendsto_zero (x : ℕ →ᵇ E) :
    Tendsto (stableSequenceValue x) atTop (𝓝 0) := by
  apply squeeze_zero_norm (norm_stableSequenceValue_le x)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_const ‖x‖

theorem stableSequenceValue_zero (x : ℕ →ᵇ E) : stableSequenceValue x 0 = x 0 := by
  simp [stableSequenceValue]

theorem stableSequenceValue_succ (x : ℕ →ᵇ E) (n : ℕ) :
    stableSequenceValue x (n + 1) = (1 / 2 : ℝ) ^ n • ((1 / 2 : ℝ) • x (n + 1)) := by
  simp only [stableSequenceValue, pow_succ, smul_smul]

theorem stableSequence_geometric_source_bound (ε r : ℝ) (hε : 0 ≤ ε)
    (hr : 0 ≤ r) (hr' : 2 * r ≤ 1) (n : ℕ) :
    (2 : ℝ) ^ n * (ε * r ^ n) ≤ ε := by
  have hp : (2 * r) ^ n ≤ (1 : ℝ) := pow_le_one₀ (by positivity) hr'
  calc
    (2 : ℝ) ^ n * (ε * r ^ n) = ε * (2 * r) ^ n := by rw [mul_pow]; ring
    _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hp hε
    _ = ε := mul_one _

end DefocusingNLS

end OAI
