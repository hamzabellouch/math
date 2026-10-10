import Mathlib

namespace OAI

noncomputable section

namespace Problem367

def binaryFusion (u v : ℝ) : ℝ := (u + v) / (1 + u * v)

def binaryFusionLoss (u v : ℝ) : ℝ :=
  u ^ 2 * v ^ 2 * (2 - u ^ 2 - v ^ 2) / (1 - u ^ 2 * v ^ 2)

theorem binaryFusion_abs_mul_lt_one {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) : |u * v| < 1 := by
  rw [abs_mul]
  calc
    |u| * |v| ≤ |u| * 1 := mul_le_mul_of_nonneg_left hv.le (abs_nonneg u)
    _ < 1 := by simpa using hu

theorem binaryFusion_denominator_pos {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) : 0 < 1 + u * v := by
  have h := (abs_lt.mp (binaryFusion_abs_mul_lt_one hu hv)).1
  linarith

theorem binaryFusionLoss_denominator_pos {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) : 0 < 1 - u ^ 2 * v ^ 2 := by
  have h := (sq_lt_one_iff_abs_lt_one (u * v)).mpr
    (binaryFusion_abs_mul_lt_one hu hv)
  nlinarith

theorem one_sub_binaryFusion_sq {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) :
    1 - binaryFusion u v ^ 2 =
      (1 - u ^ 2) * (1 - v ^ 2) / (1 + u * v) ^ 2 := by
  have hd := ne_of_gt (binaryFusion_denominator_pos hu hv)
  unfold binaryFusion
  field_simp
  ring

theorem abs_binaryFusion_lt_one {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) : |binaryFusion u v| < 1 := by
  apply (sq_lt_one_iff_abs_lt_one _).mp
  have hu' : 0 < 1 - u ^ 2 := by
    have := (sq_lt_one_iff_abs_lt_one u).mpr hu
    linarith
  have hv' : 0 < 1 - v ^ 2 := by
    have := (sq_lt_one_iff_abs_lt_one v).mpr hv
    linarith
  have hd := binaryFusion_denominator_pos hu hv
  have hpos : 0 < 1 - binaryFusion u v ^ 2 := by
    rw [one_sub_binaryFusion_sq hu hv]
    positivity
  linarith

theorem binaryFusionLoss_nonneg {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) : 0 ≤ binaryFusionLoss u v := by
  have hu' := (sq_lt_one_iff_abs_lt_one u).mpr hu
  have hv' := (sq_lt_one_iff_abs_lt_one v).mpr hv
  have hf : 0 ≤ 2 - u ^ 2 - v ^ 2 := by linarith
  have hd := binaryFusionLoss_denominator_pos hu hv
  unfold binaryFusionLoss
  positivity

theorem binaryFusion_symmetric_square {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) :
    ((u + v) ^ 2 / (1 + u * v) + (u - v) ^ 2 / (1 - u * v)) / 2 =
      u ^ 2 + v ^ 2 - binaryFusionLoss u v := by
  have hp := ne_of_gt (binaryFusion_denominator_pos hu hv)
  have hm : 1 - u * v ≠ 0 := by
    have := (abs_lt.mp (binaryFusion_abs_mul_lt_one hu hv)).2
    linarith
  have hq := ne_of_gt (binaryFusionLoss_denominator_pos hu hv)
  unfold binaryFusionLoss
  field_simp
  ring

theorem binaryFusion_symmetric_square_le {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) :
    ((u + v) ^ 2 / (1 + u * v) + (u - v) ^ 2 / (1 - u * v)) / 2 ≤
      u ^ 2 + v ^ 2 := by
  rw [binaryFusion_symmetric_square hu hv]
  exact sub_le_self _ (binaryFusionLoss_nonneg hu hv)

theorem binaryFusionLoss_lower_bound {u v theta : ℝ}
    (hu : |u| ≤ theta) (hv : |v| ≤ theta) (htheta : theta < 1) :
    2 * (1 - theta ^ 2) * u ^ 2 * v ^ 2 ≤ binaryFusionLoss u v := by
  have ht0 : 0 ≤ theta := le_trans (abs_nonneg u) hu
  have hu' : u ^ 2 ≤ theta ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg u) ht0).mpr hu
  have hv' : v ^ 2 ≤ theta ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg v) ht0).mpr hv
  have ht2 : theta ^ 2 < 1 := (sq_lt_one_iff₀ ht0).mpr htheta
  have hp : 0 ≤ u ^ 2 * v ^ 2 := mul_nonneg (sq_nonneg u) (sq_nonneg v)
  have hf : 0 ≤ 2 - u ^ 2 - v ^ 2 := by linarith
  have hd := binaryFusionLoss_denominator_pos (lt_of_le_of_lt hu htheta)
    (lt_of_le_of_lt hv htheta)
  have hfactor : 2 * (1 - theta ^ 2) ≤ 2 - u ^ 2 - v ^ 2 := by linarith
  have hnum : 0 ≤ u ^ 2 * v ^ 2 * (2 - u ^ 2 - v ^ 2) := mul_nonneg hp hf
  unfold binaryFusionLoss
  calc
    2 * (1 - theta ^ 2) * u ^ 2 * v ^ 2 =
        (u ^ 2 * v ^ 2) * (2 * (1 - theta ^ 2)) := by ring
    _ ≤ u ^ 2 * v ^ 2 * (2 - u ^ 2 - v ^ 2) :=
      mul_le_mul_of_nonneg_left hfactor hp
    _ ≤ u ^ 2 * v ^ 2 * (2 - u ^ 2 - v ^ 2) / (1 - u ^ 2 * v ^ 2) := by
      apply (le_div_iff₀ hd).mpr
      exact mul_le_of_le_one_right hnum (by linarith)

theorem binaryFusion_integrand_le_two {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) : (u + v) ^ 2 / (1 + u * v) ≤ 2 := by
  apply (div_le_iff₀ (binaryFusion_denominator_pos hu hv)).mpr
  have hu' := (sq_lt_one_iff_abs_lt_one u).mpr hu
  have hv' := (sq_lt_one_iff_abs_lt_one v).mpr hv
  nlinarith

theorem binaryFusionLoss_le_sum_sq {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) : binaryFusionLoss u v ≤ u ^ 2 + v ^ 2 := by
  have hp : 0 ≤ (u + v) ^ 2 / (1 + u * v) :=
    div_nonneg (sq_nonneg _) (binaryFusion_denominator_pos hu hv).le
  have hmden : 0 < 1 - u * v := by
    have := (abs_lt.mp (binaryFusion_abs_mul_lt_one hu hv)).2
    linarith
  have hm : 0 ≤ (u - v) ^ 2 / (1 - u * v) :=
    div_nonneg (sq_nonneg _) hmden.le
  have hid := binaryFusion_symmetric_square hu hv
  linarith

end Problem367

end

end OAI
