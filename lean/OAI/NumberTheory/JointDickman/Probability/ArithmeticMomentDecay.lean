import OAI.NumberTheory.JointDickman.Probability.ArithmeticMomentComparison
import OAI.NumberTheory.JointDickman.Amplification.ReciprocalTail

namespace OAI

/-! # The finite arithmetic moment error tends to zero at the auxiliary cutoff -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem amplification_quadratic_error_bound {B : ℕ} (hB : 1 < B) :
    6*(B : ℝ)^2*(∑ p ∈ auxiliaryPrimes B, 1 / (p : ℝ)^2) ≤ 6 / (B : ℝ) := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast (by omega : 1 ≤ B)
  have hc0 : auxiliaryCutoff B ≠ 0 := pow_ne_zero _ (by omega)
  have ht := sum_reciprocal_square_tail (auxiliaryPrimes B) hc0 (by
    intro p hp
    exact_mod_cast (mem_filter.mp hp).2)
  have hp : (B : ℝ)^3 ≤ (auxiliaryCutoff B : ℝ) := by
    simp only [auxiliaryCutoff, Nat.cast_pow]
    exact pow_le_pow_right₀ hB1 (by norm_num : 3 ≤ 1000)
  have ht' := ht.trans (one_div_le_one_div_of_le (pow_pos hB0 3) hp)
  calc
    _ ≤ 6*(B : ℝ)^2*(1 / (B : ℝ)^3) :=
      mul_le_mul_of_nonneg_left ht' (by positivity)
    _ = _ := by field_simp

theorem amplification_quadratic_error_tendsto :
    Tendsto (fun B : ℕ => 6*(B : ℝ)^2*(∑ p ∈ auxiliaryPrimes B, 1 / (p : ℝ)^2))
      atTop (nhds 0) := by
  apply squeeze_zero'
    (Eventually.of_forall (fun _ => by positivity))
    ((eventually_gt_atTop 1).mono (fun _ h => amplification_quadratic_error_bound h))
  exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

end JointDickman

end OAI
