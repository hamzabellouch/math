import OAI.Combinatorics.SharpThreshold.LowDegreeConstants
import OAI.Combinatorics.SharpThreshold.LowDegreeInfluence

namespace OAI

universe u

noncomputable section

namespace Problem313

/-- The numerical part of the biased low-degree estimate, with its original noise loss. -/
theorem low_degree_bound_of_noise_projection {ι : Type u} [Fintype ι]
    (a : ι → ℝ) (m I σ L : ℝ)
    (hm : 1 ≤ m) (hσ : 0 < σ) (hσhalf : σ ≤ 1 / 2)
    (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = I)
    (hindividual : ∀ i, a i ≤ I / m) (hL1 : L ≤ 1)
    (hprojection : L ≤ σ ^ 2 * (σ / 4) ^
      (-(2 : ℝ) * (σ * Real.log m / 64)) * ∑ i, (a i) ^ (3 / 2 : ℝ)) :
    L ≤ m ^ (-1 / 4 : ℝ) * I := by
  apply low_degree_influence_bound a m I (σ ^ 2) L hm ha hsum hindividual
    (sq_nonneg σ) (by nlinarith) hL1
  apply hprojection.trans
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul_of_nonneg_left (noise_loss_le_rpow hσ hσhalf hm) (sq_nonneg σ)
  · exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (ha i) _

/-- The Bernoulli standard deviation lies in the range required by the noise estimate. -/
theorem bernoulli_stddev_bounds {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    0 < Real.sqrt (p * (1 - p)) ∧ Real.sqrt (p * (1 - p)) ≤ 1 / 2 := by
  constructor
  · exact Real.sqrt_pos.2 (mul_pos hp (sub_pos.2 hp1))
  · apply Real.sqrt_le_iff.2
    refine ⟨by norm_num, ?_⟩
    nlinarith [sq_nonneg (p - 1 / 2)]

/-- Bias-parameter form of the numerical low-degree estimate. -/
theorem low_degree_bound_of_biased_projection {ι : Type u} [Fintype ι]
    (a : ι → ℝ) (m I p L : ℝ)
    (hm : 1 ≤ m) (hp : 0 < p) (hp1 : p < 1)
    (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = I)
    (hindividual : ∀ i, a i ≤ I / m) (hL1 : L ≤ 1)
    (hprojection : L ≤ (p * (1 - p)) * (Real.sqrt (p * (1 - p)) / 4) ^
      (-(2 : ℝ) * (Real.sqrt (p * (1 - p)) * Real.log m / 64)) *
      ∑ i, (a i) ^ (3 / 2 : ℝ)) :
    L ≤ m ^ (-1 / 4 : ℝ) * I := by
  obtain ⟨hσ, hσhalf⟩ := bernoulli_stddev_bounds hp hp1
  apply low_degree_bound_of_noise_projection a m I (Real.sqrt (p * (1 - p))) L
    hm hσ hσhalf ha hsum hindividual hL1
  simpa only [Real.sq_sqrt (le_of_lt (mul_pos hp (sub_pos.2 hp1)))] using hprojection

end Problem313

end

end OAI
