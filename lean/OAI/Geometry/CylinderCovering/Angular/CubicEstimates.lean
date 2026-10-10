import Mathlib

namespace OAI

namespace CylinderCovering.AngularCubic

theorem coarse_excess_bound {ε P : ℝ} (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (hP : P ≤ ε * P + 4 * ε ^ 2 + 4 * ε ^ 3) :
    P ≤ 12 * ε ^ 2 := by
  have hcube : ε ^ 3 ≤ ε ^ 2 / 2 := by
    nlinarith [mul_nonneg (sq_nonneg ε) (sub_nonneg.mpr hεhalf)]
  by_contra h
  have hlarge : 12 * ε ^ 2 < P := lt_of_not_ge h
  have hPnonneg : 0 ≤ P :=
    le_trans (mul_nonneg (by norm_num) (pow_nonneg hε 2)) hlarge.le
  have hprod : ε * P ≤ P / 2 := by
    nlinarith [mul_nonneg hPnonneg (sub_nonneg.mpr hεhalf)]
  nlinarith

theorem fine_excess_bound {ε Δ P A : ℝ} (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (hΔ : Δ ≤ ε ^ 2) (hP : P ≤ 12 * ε ^ 2)
    (hfine : P ≤ ε ^ 2 * A + ε * P + 2 * ε ^ 2 * P +
      4 * ε ^ 3 + 4 * ε * Δ) :
    P ≤ ε ^ 2 * A + 32 * ε ^ 3 := by
  have h₁ : ε * P ≤ 12 * ε ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hP hε]
  have h₂ : 2 * ε ^ 2 * P ≤ 24 * ε ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hP (show 0 ≤ 2 * ε ^ 2 by positivity)]
  have h₃ : 24 * ε ^ 4 ≤ 12 * ε ^ 3 := by
    nlinarith [mul_nonneg (show 0 ≤ ε ^ 3 by positivity) (sub_nonneg.mpr hεhalf)]
  have h₄ : 4 * ε * Δ ≤ 4 * ε ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hΔ (show 0 ≤ 4 * ε by positivity)]
  linarith

theorem coefficient_bound {a b q r Δ : ℝ}
    (hq : |q| ≤ 1) (hr : |r| ≤ 1) (hΔ : 0 ≤ Δ)
    (ha : |a - (1 + r ^ 2) / 2| ≤ Δ)
    (hb : |b - (1 + q ^ 2) / 2| ≤ Δ) :
    a * q ^ 2 + b * r ^ 2 ≤
      (q ^ 2 + q ^ 4) / 2 + (r ^ 2 + r ^ 4) / 2 + 2 * Δ := by
  have hq2 : q ^ 2 ≤ 1 := by
    have h := abs_le.mp hq
    nlinarith
  have hr2 : r ^ 2 ≤ 1 := by
    have h := abs_le.mp hr
    nlinarith
  have ha' : a ≤ (1 + r ^ 2) / 2 + Δ := by
    have := (abs_le.mp ha).2
    linarith
  have hb' : b ≤ (1 + q ^ 2) / 2 + Δ := by
    have := (abs_le.mp hb).2
    linarith
  have h₁ := mul_le_mul_of_nonneg_right ha' (sq_nonneg q)
  have h₂ := mul_le_mul_of_nonneg_right hb' (sq_nonneg r)
  have h₃ := mul_le_mul_of_nonneg_left hq2 hΔ
  have h₄ := mul_le_mul_of_nonneg_left hr2 hΔ
  nlinarith [sq_nonneg (q ^ 2 - r ^ 2)]

theorem profile_excess_bound {ε Δ P A D E : ℝ}
    (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2) (hΔ : Δ ≤ ε ^ 2)
    (hP : P ≤ ε ^ 2 * A + 32 * ε ^ 3) (hA : A ≤ D + E + 2 * Δ) :
    P ≤ ε ^ 2 * (D + E) + 33 * ε ^ 3 := by
  have h₁ := mul_le_mul_of_nonneg_left hA (sq_nonneg ε)
  have h₂ := mul_le_mul_of_nonneg_left hΔ (show 0 ≤ 2 * ε ^ 2 by positivity)
  have h₃ : 2 * ε ^ 4 ≤ ε ^ 3 := by
    nlinarith [mul_nonneg (show 0 ≤ ε ^ 3 by positivity) (sub_nonneg.mpr hεhalf)]
  nlinarith

theorem no_joint_failure {ε P D E : ℝ} (hε : 0 < ε)
    (hP : P ≤ ε ^ 2 * (D + E) + 33 * ε ^ 3) :
    ¬ (ε ^ 2 * D + 100 * ε ^ 3) +
      (ε ^ 2 * E + 100 * ε ^ 3) < P := by
  have hcube : 0 < ε ^ 3 := pow_pos hε 3
  nlinarith

end CylinderCovering.AngularCubic

end OAI
