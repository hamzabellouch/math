import OAI.Analysis.IrrationalRotation.Model.CircleParameters
import OAI.Analysis.IrrationalRotation.Analysis.ParameterTails
import OAI.Analysis.IrrationalRotation.Sampling.SamplingHorizon

namespace OAI

namespace Invariant233
open Filter
open scoped Topology

namespace CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem shifted_K_pos (n : ℕ) : 0 < (p.K (n + 1) : ℝ) := by
  exact_mod_cast hp.K_pos (n + 1) (by omega)

theorem shifted_K_double (n : ℕ) :
    2 * (p.K (n + 1) : ℝ) ≤ (p.K (n + 1 + 1) : ℝ) := by
  exact_mod_cast (hp.K_double (n + 1) (by omega)).le

theorem summable_reciprocal : Summable (fun n : ℕ => 1 / (p.K (n + 1) : ℝ)) :=
  ParameterTails.summable_reciprocal hp.shifted_K_pos hp.shifted_K_double

theorem reciprocal_tail_bound (j : ℕ) (hj : 1 ≤ j) :
    (∑' n : ℕ, 1 / (p.K (j + 1 + n) : ℝ)) ≤ 2 / (p.K (j + 1) : ℝ) := by
  have h := ParameterTails.reciprocal_tail_bound hp.shifted_K_pos hp.shifted_K_double (j - 1)
  simpa only [Nat.sub_add_cancel hj, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem summable_partition_cost :
    Summable (fun n : ℕ => (1 + (p.height (n + 1) : ℝ)) / p.K (n + 1)) := by
  apply ParameterTails.summable_partition_cost hp.shifted_K_pos hp.shifted_K_double
    (fun n => Nat.cast_nonneg (p.height (n + 1)))
  intro n
  have hh := hp.continuity_height (n + 1) (by omega)
  have hpow : (1 / 2 : ℝ) ^ (n + 1) ≤ (1 / 2 : ℝ) ^ n := by
    rw [pow_succ]
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) n]
  exact hh.trans hpow

theorem tendsto_sampling_horizon :
    Tendsto (fun n : ℕ => p.Q (n + 1) / p.K (n + 2)) atTop (𝓝 0) := by
  apply SamplingHorizon.tendsto_horizon_ratio_of_pow_two_le
    (m := fun n => (p.m (n + 1) : ℝ)) (K := fun n => (p.K (n + 1) : ℝ))
  · intro n
    have hm : (2 : ℝ) ^ (n + 1) ≤ (p.m (n + 1) : ℝ) := by
      exact_mod_cast hp.m_ge_pow (n + 1) (by omega)
    have ht : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (n + 1) := by
      rw [pow_succ]
      nlinarith [pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) n]
    exact ht.trans hm
  · intro n
    rw [hp.next_K (n + 1) (by omega)]
    exact Nat.le_ceil _

end CircleParameterLaws
end Invariant233

end OAI
