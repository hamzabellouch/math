import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDyadicMean
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityBlockCauchy

namespace OAI

/-! # Summable weights for the actual dyadic-square estimates -/

namespace Ostmann

open scoped BigOperators

 theorem density_block_weight_sum (J : ℕ) :
    (∑ j ∈ Finset.range J, (3 / 4 : ℝ) ^ j) ≤ 4 := by
  have h := (summable_geometric_of_abs_lt_one (by norm_num : |(3 / 4 : ℝ)| < 1)).sum_le_tsum
    (Finset.range J) (fun _ _ => by positivity)
  have he : (∑' j : ℕ, (3 / 4 : ℝ) ^ j) = 4 := by
    rw [tsum_geometric_of_abs_lt_one (by norm_num : |(3 / 4 : ℝ)| < 1)]
    norm_num
  exact h.trans_eq he

 theorem density_block_energy_summable :
    Summable (fun j : ℕ => (j + 2 : ℝ) ^ 3 * (2 / 3 : ℝ) ^ j) := by
  have h3 := summable_pow_mul_geometric_of_norm_lt_one 3 (by norm_num : ‖(2 / 3 : ℝ)‖ < 1)
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 (by norm_num : ‖(2 / 3 : ℝ)‖ < 1)
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num : ‖(2 / 3 : ℝ)‖ < 1)
  have h0 := summable_geometric_of_abs_lt_one (by norm_num : |(2 / 3 : ℝ)| < 1)
  convert ((h3.add (h2.mul_left 6)).add (h1.mul_left 12)).add (h0.mul_left 8) using 1
  funext j
  ring

noncomputable def densityBlockEnergyConstant : ℝ :=
  ∑' j : ℕ, (j + 2 : ℝ) ^ 3 * (2 / 3 : ℝ) ^ j

 theorem densityBlockEnergyConstant_pos : 0 < densityBlockEnergyConstant := by
  unfold densityBlockEnergyConstant
  have h := density_block_energy_summable.le_tsum 0 (fun _ _ => by positivity)
  norm_num at h
  linarith

 theorem density_block_energy_sum (J : ℕ) :
    (∑ j ∈ Finset.range J, ((j + 2 : ℝ) ^ 3 / (2 : ℝ) ^ j) / (3 / 4 : ℝ) ^ j) ≤
      densityBlockEnergyConstant := by
  have he (j : ℕ) : ((j + 2 : ℝ) ^ 3 / (2 : ℝ) ^ j) / (3 / 4 : ℝ) ^ j =
      (j + 2 : ℝ) ^ 3 * (2 / 3 : ℝ) ^ j := by
    rw [div_div, ← mul_pow]
    have hmul : (2 : ℝ) * (3 / 4) = 3 / 2 := by norm_num
    rw [hmul, div_eq_mul_inv, ← inv_pow]
    norm_num
  simp_rw [he]
  exact density_block_energy_summable.sum_le_tsum (Finset.range J) (fun _ _ => by positivity)

end Ostmann

end OAI
