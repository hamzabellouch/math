import OAI.Combinatorics.ExpectationThreshold.ScaleBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

/-!
# The mean of the numerical color variable

The variable at color `c` is `512^4 / 512^(c.val+1)`. This quotient represents
a possibly negative integral exponent without natural
subtraction. The computation includes the residual last color and also
applies when the selected number of scales is zero.
-/

namespace TalagrandThreshold

open scoped BigOperators

private theorem color_mean_row (p : ℝ) (n : ℕ) :
    ((256 : ℝ) ^ n * p) * ((512 : ℝ) ^ 4 / (512 : ℝ) ^ n) =
      (512 : ℝ) ^ 4 * (p * (1 / 2 : ℝ) ^ n) := by
  have hratio : (256 : ℝ) ^ n / (512 : ℝ) ^ n = (1 / 2 : ℝ) ^ n := by
    rw [← div_pow]
    norm_num
  calc
    _ = (512 : ℝ) ^ 4 * (p * ((256 : ℝ) ^ n / (512 : ℝ) ^ n)) := by ring
    _ = _ := by rw [hratio]

/-- The exact finite-color mean, including the residual last color. -/
theorem color_mean_eq (p : ℝ) (s : ℕ) :
    (∑ c : Color s,
      colorProb p s c * ((512 : ℝ) ^ 4 / (512 : ℝ) ^ (c.val + 1))) =
      (512 : ℝ) ^ 4 *
        (p * (∑ i : Fin s, (1 / 2 : ℝ) ^ (i.val + 1)) +
          (1 - p * scaleSum s) * (1 / (512 : ℝ) ^ (s + 1))) := by
  change (∑ c : Fin (s + 1),
      colorProb p s c * ((512 : ℝ) ^ 4 / (512 : ℝ) ^ (c.val + 1))) = _
  rw [Fin.sum_univ_castSucc]
  simp only [colorProb_castSucc, colorProb_last, Fin.val_castSucc, Fin.val_last]
  simp_rw [color_mean_row]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- Maximality of the scale makes the common mean at most `5 * 512^4 * p`. -/
theorem color_mean_le {p : ℝ} (hp : 0 < p) {s : ℕ}
    (_hs : p * scaleSum s ≤ 1 / 2)
    (hnext : 1 / 2 < p * scaleSum (s + 1)) :
    (∑ c : Color s,
      colorProb p s c * ((512 : ℝ) ^ 4 / (512 : ℝ) ^ (c.val + 1))) ≤
      5 * (512 : ℝ) ^ 4 * p := by
  have hres : 1 - p * scaleSum s ≤ 1 :=
    sub_le_self _ (mul_nonneg hp.le (scaleSum_nonneg s))
  have htail : (1 - p * scaleSum s) * (1 / (512 : ℝ) ^ (s + 1)) ≤ 4 * p := by
    calc
      _ ≤ 1 * (1 / (512 : ℝ) ^ (s + 1)) :=
        mul_le_mul_of_nonneg_right hres (by positivity)
      _ ≤ 4 * p := by
        simpa only [one_mul] using (tail_lt_four_mul_p hp hnext).le
  rw [color_mean_eq]
  calc
    _ ≤ (512 : ℝ) ^ 4 * (p * 1 + 4 * p) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left (half_geometric_sum_le_one s) hp.le) htail)
        (by positivity)
    _ = 5 * (512 : ℝ) ^ 4 * p := by ring

theorem rounding_constant_pos : 0 < (25 : ℝ) * (512 : ℝ) ^ 4 := by positivity

/-- The leading constant is 25. -/
theorem five_Bfour_mul_scaled_density (r : ℝ) :
    5 * (512 : ℝ) ^ 4 * (r / ((25 : ℝ) * (512 : ℝ) ^ 4)) = r / 5 := by
  field_simp
  ring

/-- The mean bound at the exact density used for rounding. -/
theorem color_mean_le_r_div_five {r : ℝ} (hr : 0 < r) {s : ℕ}
    (hs : (r / ((25 : ℝ) * (512 : ℝ) ^ 4)) * scaleSum s ≤ 1 / 2)
    (hnext : 1 / 2 < (r / ((25 : ℝ) * (512 : ℝ) ^ 4)) * scaleSum (s + 1)) :
    (∑ c : Color s,
      colorProb (r / ((25 : ℝ) * (512 : ℝ) ^ 4)) s c *
        ((512 : ℝ) ^ 4 / (512 : ℝ) ^ (c.val + 1))) ≤ r / 5 := by
  simpa only [five_Bfour_mul_scaled_density] using
    color_mean_le (div_pos hr rounding_constant_pos) hs hnext

end TalagrandThreshold

end OAI
