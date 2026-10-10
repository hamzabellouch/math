import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.RegularLatticeScales
import OAI.Analysis.RieszRectifiability.Foundations.DyadicPropagationRadii

namespace OAI

/-!
# Comparing lattice generations with dyadic descendants

One lattice generation contracts the radius by `64`, hence corresponds to six
dyadic halvings. Dividing a dyadic depth by six separates a whole lattice
generation from a bounded remainder, giving uniform comparisons of the two scales.
-/

namespace RieszRectifiability

noncomputable section

/-- Advancing `t` lattice generations is exactly `6 * t` dyadic halvings. -/
theorem latticeRadius_eq_descendantRadius (R : ℝ) (k t : ℕ) :
    latticeRadius R (k + t) = descendantRadius (latticeRadius R k) (6 * t) := by
  rw [latticeRadius_add]
  change latticeRadius R k * (1 / 64 : ℝ) ^ t = latticeRadius R k / (2 : ℝ) ^ (6 * t)
  norm_num [pow_mul, one_div_pow, div_eq_mul_inv]

/-- The remainder modulo six records the dyadic contraction within a lattice generation. -/
theorem descendantRadius_cell_remainder (R H : ℝ) (k j : ℕ) :
    descendantRadius (H * latticeRadius R k) j =
      H * latticeRadius R (k + j / 6) / (2 : ℝ) ^ (j % 6) := by
  have hj : j = 6 * (j / 6) + j % 6 := by omega
  have hp : (2 : ℝ) ^ j = (2 : ℝ) ^ (6 * (j / 6)) * (2 : ℝ) ^ (j % 6) := by
    rw [← pow_add, ← hj]
  rw [latticeRadius_eq_descendantRadius]
  simp only [descendantRadius, hp]
  field_simp

/-- Positive dyadic descendant radii lie between fixed multiples of the matching lattice scale. -/
theorem descendantRadius_cell_bounds (R H : ℝ) (hR : 0 < R) (hH : 0 < H) (k j : ℕ) :
    (H / 64) * latticeRadius R (k + j / 6) ≤ descendantRadius (H * latticeRadius R k) j ∧
      descendantRadius (H * latticeRadius R k) j ≤ H * latticeRadius R (k + j / 6) := by
  rw [descendantRadius_cell_remainder]
  have hr := latticeRadius_pos R hR (k + j / 6)
  have hp : 0 < (2 : ℝ) ^ (j % 6) := by positivity
  have hlo : 1 ≤ (2 : ℝ) ^ (j % 6) := one_le_pow₀ (by norm_num)
  have hhi : (2 : ℝ) ^ (j % 6) ≤ 64 := by
    have ht := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (show j % 6 ≤ 6 by omega)
    norm_num at ht
    exact ht
  constructor
  · apply (le_div_iff₀ hp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hhi (mul_pos hH hr).le]
  · apply (div_le_iff₀ hp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlo (mul_pos hH hr).le]

end

end RieszRectifiability

end OAI
