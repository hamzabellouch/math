import Mathlib

namespace OAI

namespace RadialFreezing

theorem collar_gt_radial {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    A < 2 * (A + B) + 1 := by
  linarith

theorem collar_length_pos {A B R d : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 ≤ R) (hd : 0 < d) :
    0 < R + (A + (2 * (A + B) + 1)) * d := by
  have hC : 0 < A + (2 * (A + B) + 1) := by linarith
  exact add_pos_of_nonneg_of_pos hR (mul_pos hC hd)

theorem footprint_subset_triangle {A B R d u v m : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hd : 0 ≤ d)
    (hu_lower : -A * d ≤ u) (hu_upper : u ≤ R + A * d)
    (hv : |v - m * u| ≤ d / 2 * |u| + B * d ^ 2) :
    -(2 * (A + B) + 1) * d ≤ u ∧
      u ≤ R + A * d ∧
      |v - m * u| ≤ d / 2 * (u + (2 * (A + B) + 1) * d) := by
  have hC : A ≤ 2 * (A + B) + 1 := le_of_lt (collar_gt_radial hA hB)
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hC) hd]
  constructor
  · exact hu_upper
  · apply hv.trans
    by_cases hu : 0 ≤ u
    · rw [abs_of_nonneg hu]
      nlinarith [sq_nonneg d, mul_nonneg hA (sq_nonneg d)]
    · rw [abs_of_neg (lt_of_not_ge hu)]
      have hmul : 0 ≤ d * (u + A * d) :=
        mul_nonneg hd (by linarith)
      nlinarith [sq_nonneg d]

theorem footprint_of_transverse_error {B d u v t m : ℝ}
    (ht : |t - m| ≤ d / 2)
    (htrans : |v - t * u| ≤ B * d ^ 2) :
    |v - m * u| ≤ d / 2 * |u| + B * d ^ 2 := by
  calc
    |v - m * u| = |(v - t * u) + (t - m) * u| := by ring_nf
    _ ≤ |v - t * u| + |(t - m) * u| := abs_add_le _ _
    _ = |v - t * u| + |t - m| * |u| := by rw [abs_mul]
    _ ≤ B * d ^ 2 + (d / 2) * |u| :=
      add_le_add htrans (mul_le_mul_of_nonneg_right ht (abs_nonneg u))
    _ = d / 2 * |u| + B * d ^ 2 := by ring

theorem intercept_subset_triangle {A B R d ρ u v t m : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hd : 0 ≤ d)
    (hρ0 : 0 ≤ ρ) (hρR : ρ ≤ R)
    (hradial : |u - ρ| ≤ A * d)
    (ht : |t - m| ≤ d / 2)
    (htrans : |v - t * u| ≤ B * d ^ 2) :
    -(2 * (A + B) + 1) * d ≤ u ∧
      u ≤ R + A * d ∧
      |v - m * u| ≤ d / 2 * (u + (2 * (A + B) + 1) * d) := by
  rcases abs_le.mp hradial with ⟨hleft, hright⟩
  apply footprint_subset_triangle hA hB hd
  · linarith
  · linarith
  · exact footprint_of_transverse_error ht htrans

end RadialFreezing

end OAI
