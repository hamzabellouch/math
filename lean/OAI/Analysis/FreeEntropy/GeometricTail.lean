import OAI.Analysis.FreeEntropy.WickCoefficients

namespace OAI

noncomputable section
namespace FiniteEntropySeparation
open Finset

def geometricCumulantTail (K u : ℝ) (k : ℕ) : ℝ :=
  if 2 ≤ k then u⁻¹^k * K^(2*(k+1)) else 0
 theorem geometricCumulantTail_nonneg (K u : ℝ) (hu : 0 ≤ u) (k : ℕ) :
    0 ≤ geometricCumulantTail K u k := by
  unfold geometricCumulantTail
  split_ifs
  · exact mul_nonneg (pow_nonneg (inv_nonneg.mpr hu) _) (pow_nonneg (sq_nonneg K) (k+1) |>.trans_eq (pow_mul K 2 (k+1)).symm)
  · rfl
 theorem geometricCumulantTail_factor (K u : ℝ) (k : ℕ) :
    u⁻¹^k * K^(2*(k+1)) = K^2 * (K^2/u)^k := by
  rw [Nat.mul_add, pow_add, pow_mul, div_pow, div_eq_mul_inv, inv_pow]
  ring
 theorem geometricCumulantTail_shift (K u : ℝ) (k : ℕ) :
    geometricCumulantTail K u (k+2) = (K^6/u^2) * (K^2/u)^k := by
  rw [geometricCumulantTail, ite_eq_left (by omega), geometricCumulantTail_factor, pow_add]
  rw [div_pow, div_eq_mul_inv, div_eq_mul_inv]
  ring
 theorem geometricCumulantTail_summable {K u : ℝ} (hu : 0 < u) (hk : K^2 < u) :
    Summable (geometricCumulantTail K u) := by
  have hr : ‖K^2/u‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hu.le)]
    exact (div_lt_one hu).mpr hk
  apply (summable_nat_add_iff 2).mp
  simp_rw [geometricCumulantTail_shift]
  exact (summable_geometric_of_norm_lt_one hr).mul_left _
 theorem geometricCumulantTail_tsum {K u : ℝ} (hu : 0 < u) (hk : K^2 < u) :
    ∑' k, geometricCumulantTail K u k = (K^6/u^2) * (1-K^2/u)⁻¹ := by
  have hh := geometricCumulantTail_summable hu hk
  have hr : ‖K^2/u‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hu.le)]
    exact (div_lt_one hu).mpr hk
  rw [← hh.sum_add_tsum_nat_add 2]
  have hz : ∑ i ∈ range 2, geometricCumulantTail K u i = 0 := by
    norm_num [sum_range_succ, geometricCumulantTail]
  rw [hz, zero_add]
  simp_rw [geometricCumulantTail_shift]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hr]
 theorem geometricCumulantTail_le {K u : ℝ} (hu : 0 < u) (hk : 2*K^2 ≤ u) :
    ∑' k, geometricCumulantTail K u k ≤ 2*K^6/u^2 := by
  have hk' : K^2 < u := by nlinarith [sq_nonneg K]
  rw [geometricCumulantTail_tsum hu hk']
  have hr : K^2/u ≤ 1/2 := (div_le_iff₀ hu).mpr (by linarith)
  have hd : 0 < 1 - K^2/u := by linarith
  have hi : (1-K^2/u)⁻¹ ≤ 2 := by
    rw [← one_div]
    exact (div_le_iff₀ hd).mpr (by linarith)
  calc
    _ ≤ (K^6/u^2) * 2 := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = _ := by ring
end FiniteEntropySeparation

end

end OAI
