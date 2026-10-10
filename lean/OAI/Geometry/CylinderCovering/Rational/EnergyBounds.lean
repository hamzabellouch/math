import OAI.Geometry.CylinderCovering.Rational.FieldDefinitions

namespace OAI

namespace SlopeRational

open Set MeasureTheory

theorem rational_component_bounds {d Y T : ℝ} (hd : 0 < d)
    (hw : 2 * |Y| ≤ radius T) :
    -(1 / 8 : ℝ) ≤ a d Y T ∧ a d Y T ≤ 0 ∧ |b d Y T| ≤ 1 / 4 := by
  have hr : 0 ≤ radius T := (by positivity : 0 ≤ 2 * |Y|).trans hw
  have hden : 0 < radius T + d := by linarith
  have hs : 0 < (radius T + d) ^ 2 := sq_pos_of_pos hden
  have hY : Y ^ 2 ≤ (radius T) ^ 2 / 4 := by
    have hp := sq_le_sq₀ (by positivity : 0 ≤ 2 * |Y|) hr |>.2 hw
    nlinarith only [hp, sq_abs Y]
  have hfirst : 0 ≤ Y ^ 2 / (4 * (radius T + d) ^ 2) := by positivity
  have hsecond : 0 ≤ radius T * (radius T + 2 * d) / (16 * (radius T + d) ^ 2) := by positivity
  have hfirst_le : Y ^ 2 / (4 * (radius T + d) ^ 2) ≤ 1 / 16 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * (radius T + d) ^ 2)).2
    nlinarith [mul_nonneg hr hd.le, sq_nonneg d]
  have hsecond_le : radius T * (radius T + 2 * d) / (16 * (radius T + d) ^ 2) ≤ 1 / 16 := by
    apply (div_le_iff₀ (by positivity : 0 < 16 * (radius T + d) ^ 2)).2
    nlinarith [sq_nonneg d]
  refine ⟨?_, ?_, ?_⟩
  · unfold a
    rw [neg_div]
    linarith
  · unfold a
    rw [neg_div]
    linarith
  · unfold b
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * (radius T + d))]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (radius T + d))).2
    linarith

theorem rational_energy_bounds {d : ℝ} (hd : 0 < d) {z : Plane} (hz : z ∈ wedge) :
    0 ≤ a d (z 0) (z 1) ^ 2 + (1 / 2) * b d (z 0) (z 1) ^ 2 ∧
    a d (z 0) (z 1) ^ 2 + (1 / 2) * b d (z 0) (z 1) ^ 2 ≤ 3 / 64 := by
  obtain ⟨ha, ha0, hb⟩ := rational_component_bounds hd hz
  have ha2 : a d (z 0) (z 1) ^ 2 ≤ 1 / 64 := by nlinarith
  have hb' := abs_le.mp hb
  have hb2 : b d (z 0) (z 1) ^ 2 ≤ 1 / 16 := by nlinarith [hb'.1, hb'.2]
  exact ⟨by positivity, by linarith⟩

theorem rational_energy_measurable (d : ℝ) :
    Measurable (fun z : Plane => a d (z 0) (z 1) ^ 2 + (1 / 2) * b d (z 0) (z 1) ^ 2) := by
  unfold a b radius
  fun_prop

end SlopeRational

end OAI
