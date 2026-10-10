import OAI.Geometry.EinsteinFour.Jacobi
import OAI.Geometry.EinsteinFour.VolumeConstants

namespace OAI

/-! Comparison of the piecewise polynomial integration weight with the exact
Jacobi determinant-loss coefficient. The variable is `u = t / pi`. -/

namespace PositiveEinsteinFour.Jacobi

open VolumeConstants

noncomputable section

def radialLower (u : ℝ) : ℝ :=
  if u ≤ 5 / 8 then initialFactor u else 15 / 16

private theorem small_parameter_bound {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 25 / 64) :
    x ^ 2 * (3 + 5 * x + 6 * x ^ 2) ≤ lossFactor (x / (1 - x)) := by
  have hden : 0 < 1 - x := by linarith
  have hcap : x ^ 2 * (3 + 5 * x + 6 * x ^ 2) ≤ 1 := by
    calc
      _ ≤ (25 / 64 : ℝ) ^ 2 * (3 + 5 * (25 / 64) + 6 * (25 / 64) ^ 2) := by
        gcongr
      _ ≤ 1 := by norm_num
  have hid : (1 - x) ^ 3 *
      ((x / (1 - x)) ^ 2 * (3 - x / (1 - x)) - x ^ 2 * (3 + 5 * x + 6 * x ^ 2)) =
      x ^ 5 * (3 - 2 * x) * (2 - 3 * x) := by
    field_simp [ne_of_gt hden]
    ring
  have hpos : 0 ≤ x ^ 5 * (3 - 2 * x) * (2 - 3 * x) := by
    apply mul_nonneg
    · exact mul_nonneg (pow_nonneg hx _) (by linarith)
    · linarith
  have hdiff : x ^ 2 * (3 + 5 * x + 6 * x ^ 2) ≤
      (x / (1 - x)) ^ 2 * (3 - x / (1 - x)) := by
    have hproduct : 0 ≤ (1 - x) ^ 3 *
        ((x / (1 - x)) ^ 2 * (3 - x / (1 - x)) - x ^ 2 * (3 + 5 * x + 6 * x ^ 2)) := by
      rwa [hid]
    have h := nonneg_of_mul_nonneg_right hproduct (pow_pos hden 3)
    linarith
  apply le_min hcap
  exact hdiff.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (sq_nonneg _))

private theorem large_parameter_bound {β : ℝ} (hβ : 25 / 39 ≤ β) :
    (15 / 16 : ℝ) ≤ lossFactor β := by
  have hβ0 : 0 ≤ β := by linarith
  apply le_min (by norm_num)
  by_cases hβ1 : 1 ≤ β
  · have hs : 1 ≤ β ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left (le_max_left (1 : ℝ) (3 - β)) (sq_nonneg β)
    nlinarith only [hs, hm]
  · have hβ1' : β ≤ 1 := (lt_of_not_ge hβ1).le
    have hs : β ^ 2 ≤ β := by nlinarith
    have hbr : β * (25 / 39) ≤ 25 / 39 := by linarith
    have hcoef : 0 ≤ 3 * (β + 25 / 39) - β ^ 2 - β * (25 / 39) - (25 / 39) ^ 2 := by
      nlinarith
    have hp := mul_nonneg (sub_nonneg.mpr hβ) hcoef
    have hcubic : (15 / 16 : ℝ) ≤ β ^ 2 * (3 - β) := by nlinarith only [hp]
    exact hcubic.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (sq_nonneg _))

/-- The full piecewise lower weight is valid on the preconjugate radial
interval. Its jump at `5/8` is intentional and included in the proof. -/
theorem radialLower_le_lossFactor {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) :
    radialLower u ≤ lossFactor (u ^ 2 / (1 - u ^ 2)) := by
  have hden : 0 < 1 - u ^ 2 := by nlinarith
  by_cases hh : u ≤ 5 / 8
  · rw [radialLower, ite_eq_left hh]
    have h := small_parameter_bound (sq_nonneg u) (by nlinarith [sq_nonneg (u - 5 / 8)])
    have hid : initialFactor u = (u ^ 2) ^ 2 * (3 + 5 * u ^ 2 + 6 * (u ^ 2) ^ 2) := by
      unfold initialFactor
      ring
    rwa [hid]
  · rw [radialLower, ite_eq_right hh]
    apply large_parameter_bound
    apply (le_div_iff₀ hden).2
    nlinarith [sq_nonneg (u - 5 / 8)]

end

end PositiveEinsteinFour.Jacobi

end OAI
