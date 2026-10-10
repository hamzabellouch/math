import OAI.InformationTheory.BooleanNoise.CurvatureBounds
import OAI.InformationTheory.SoftChannel.CurvatureCertificates

namespace OAI

section

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

def CurvatureBounds_smallCoarseBound (z : ℝ) : ℝ :=
  ((4 / 3) + (2 / 3) * (z / (1 - z))) / ((1 - z) ^ 2 * (1 + z / 3) ^ 3)

theorem CurvatureBounds_smallCoarseBound_lt_ten_sevenths {z : ℝ}
    (hz0 : 0 ≤ z) (hz25 : z ≤ 1 / 25) : CurvatureBounds_smallCoarseBound z < 10 / 7 := by
  have hz1 : 0 < 1 - z := by linarith
  have hratio : z / (1 - z) ≤ 1 / 24 := (div_le_iff₀ hz1).mpr (by linarith)
  have hnum : (4 / 3 : ℝ) + (2 / 3) * (z / (1 - z)) ≤ 49 / 36 := by linarith
  have hzsq : z ^ 2 ≤ 1 / 625 := by
    nlinarith [mul_nonneg hz0 (show 0 ≤ 1 / 25 - z by linarith)]
  have hcube : 1 + z ≤ (1 + z / 3) ^ 3 := by
    nlinarith [sq_nonneg z, pow_nonneg hz0 3]
  have hbase : (599 / 625 : ℝ) ≤ (1 - z) ^ 2 * (1 + z) := by
    nlinarith [pow_nonneg hz0 3]
  have hden : (599 / 625 : ℝ) ≤ (1 - z) ^ 2 * (1 + z / 3) ^ 3 :=
    hbase.trans (mul_le_mul_of_nonneg_left hcube (sq_nonneg _))
  have hden0 : 0 < (1 - z) ^ 2 * (1 + z / 3) ^ 3 := by linarith
  apply (div_lt_iff₀ hden0).mpr
  calc
    (4 / 3 : ℝ) + (2 / 3) * (z / (1 - z)) ≤ 49 / 36 := hnum
    _ < (10 / 7) * (599 / 625) := by norm_num
    _ ≤ (10 / 7) * ((1 - z) ^ 2 * (1 + z / 3) ^ 3) :=
      mul_le_mul_of_nonneg_left hden (by norm_num)

theorem CurvatureBounds_normalized_small_curvature_le {z a : ℝ}
    (hz0 : 0 < z) (hz25 : z ≤ 1 / 25)
    (hal : 1 + z / 3 ≤ a) (hau : a ≤ 1 + z / (3 * (1 - z))) :
    (((1 + z) * a - 1) / z) / ((1 - z) ^ 2 * a ^ 3) ≤ CurvatureBounds_smallCoarseBound z := by
  have hz1 : 0 < 1 - z := by linarith
  have ha0 : 0 < a := by linarith
  have hnum : ((1 + z) * a - 1) / z ≤ (4 / 3) + (2 / 3) * (z / (1 - z)) := by
    calc
      ((1 + z) * a - 1) / z ≤
          ((1 + z) * (1 + z / (3 * (1 - z))) - 1) / z :=
        div_le_div_of_nonneg_right
          (sub_le_sub_right (mul_le_mul_of_nonneg_left hau (by linarith)) 1) hz0.le
      _ = (4 / 3) + (2 / 3) * (z / (1 - z)) := by
        field_simp [hz0.ne', hz1.ne']
        ring
  have hupper0 : 0 ≤ (4 / 3 : ℝ) + (2 / 3) * (z / (1 - z)) := by positivity
  have hden0 : 0 < (1 - z) ^ 2 * (1 + z / 3) ^ 3 := by positivity
  have hdena0 : 0 < (1 - z) ^ 2 * a ^ 3 := by positivity
  have hdencmp : (1 - z) ^ 2 * (1 + z / 3) ^ 3 ≤ (1 - z) ^ 2 * a ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hal 3) (sq_nonneg _)
  calc
    (((1 + z) * a - 1) / z) / ((1 - z) ^ 2 * a ^ 3) ≤
        ((4 / 3) + (2 / 3) * (z / (1 - z))) / ((1 - z) ^ 2 * a ^ 3) :=
      div_le_div_of_nonneg_right hnum hdena0.le
    _ ≤ CurvatureBounds_smallCoarseBound z := div_le_div_of_nonneg_left hupper0 hden0 hdencmp

end LeanBlast.CourtadeKumar
end
end

end OAI
