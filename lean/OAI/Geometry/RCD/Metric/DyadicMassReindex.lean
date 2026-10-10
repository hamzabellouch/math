import OAI.Geometry.RCD.Heat.GaussianUpperHeatIncrement
import OAI.Geometry.RCD.Heat.HeatExteriorDecay
import OAI.Geometry.RCD.Coordinates.NormalizationRebase

namespace OAI

/-! # Converting outward Gaussian shells to inward dyadic mass envelopes -/

open scoped BigOperators

noncomputable section

namespace RegularPointCoordinates

/-- The ancestor radius in an outward shell is exactly the corresponding
fixed-root dyadic radius. -/
theorem outward_radius_eq_ancestor {s R : ℝ} {N j : ℕ}
    (hR : (2 : ℝ) ^ N * s = R) (hj : j ≤ N) :
    (2 : ℝ) ^ (N - j) * s = R / (2 : ℝ) ^ j := by
  apply (eq_div_iff (pow_ne_zero j (by norm_num : (2 : ℝ) ≠ 0))).mpr
  rw [← hR]
  calc
    _ = ((2 : ℝ) ^ (N - j) * 2 ^ j) * s := by ring
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel hj]

/-- Reversing the finite shell sum produces the geometric convolution
of the actual masses at the fixed-root dyadic radii. -/
theorem outward_sum_eq_inward_sum (f : ℝ → ℝ) (β : ℝ) {s R : ℝ} (N : ℕ)
    (hR : (2 : ℝ) ^ N * s = R) :
    (∑ j ∈ Finset.range (N + 1), β ^ j * f (2 ^ j * s)) =
      ∑ j ∈ Finset.range (N + 1), β ^ (N - j) * f (R / 2 ^ j) := by
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hi : N + 1 - 1 - j = N - j := by omega
  simp only [hi, outward_radius_eq_ancestor hR hjN]

/-- The scalar regularizer is also bounded by the same geometric
background envelope when the outer radius is fixed. -/
theorem dyadic_square_le_three_quarters {s R : ℝ} (hs : 0 ≤ s) (N : ℕ)
    (hR : (2 : ℝ) ^ N * s = R) :
    s ^ 2 ≤ R ^ 2 * (3 / 4 : ℝ) ^ N := by
  have hreg := dyadic_regularizer_le_geometric (lambda := 1) hs N hR.le
  simp only [one_mul, abs_of_nonneg (sq_nonneg s), abs_one] at hreg
  have hfirst : s ^ 2 ≤ s ^ 2 * (2 : ℝ) ^ N :=
    le_mul_of_one_le_right (sq_nonneg s) (one_le_pow₀ (by norm_num))
  have hpow : (1 / 2 : ℝ) ^ N ≤ (3 / 4 : ℝ) ^ N :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) N
  exact hfirst.trans (hreg.trans (mul_le_mul_of_nonneg_left hpow (sq_nonneg R)))

end RegularPointCoordinates

end

end OAI
