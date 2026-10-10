import OAI.NumberTheory.TwoPoint.Fourier.MinorArcGeometric
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace OAI

/-! Convert the exact geometric denominator to distance from the nearest
integer. This is the kernel used in the rational-spacing estimate. -/

namespace TwoPointCorrelations

open Complex

lemma minor_arc_phase_gap (α : ℝ) :
    4 * ‖(α : UnitAddCircle)‖ ≤ ‖additiveCharacter α 1 - 1‖ := by
  let δ := α - (round α : ℝ)
  have hδ : |δ| ≤ 1 / 2 := by
    simpa only [UnitAddCircle.norm_eq, abs_one] using
      (AddCircle.norm_le_half_period (1 : ℝ) (by norm_num) (x := (α : UnitAddCircle)))
  have hsin := Real.mul_abs_le_abs_sin (x := Real.pi * δ) (by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos])
  have hs : |Real.sin (Real.pi * δ)| = |Real.sin (Real.pi * α)| := by
    rw [show Real.pi * δ = Real.pi * α - (round α : ℝ) * Real.pi by dsimp [δ]; ring,
      Real.sin_sub_int_mul_pi, abs_mul, abs_zpow]
    norm_num
  have hn : ‖additiveCharacter α 1 - 1‖ = 2 * |Real.sin (Real.pi * α)| := by
    have he : additiveCharacter α 1 = Complex.exp (Complex.I * ((2 * Real.pi * α : ℝ) : ℂ)) := by
      simp only [additiveCharacter, Nat.cast_one, mul_one]
      rw [mul_comm]
    rw [he, Complex.norm_exp_I_mul_ofReal_sub_one,
      show 2 * Real.pi * α / 2 = Real.pi * α by ring,
      Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [hn, ← hs, UnitAddCircle.norm_eq]
  have hδπ : |Real.pi * δ| = Real.pi * |δ| := by rw [abs_mul, abs_of_pos Real.pi_pos]
  rw [hδπ] at hsin
  have he : (2 / Real.pi) * (Real.pi * |δ|) = 2 * |δ| := by field_simp
  rw [he] at hsin
  change 4 * |δ| ≤ 2 * |Real.sin (Real.pi * δ)|
  linarith

lemma minor_arc_geometric_circle {α L : ℝ} (hα : 0 < ‖(α : UnitAddCircle)‖) :
    minorArcGeometricBound L α ≤ min L (1 / (2 * ‖(α : UnitAddCircle)‖)) := by
  have hgap := minor_arc_phase_gap α
  have hn : 0 < ‖additiveCharacter α 1 - 1‖ := by linarith
  have hz : additiveCharacter α 1 ≠ 1 := by
    intro he
    simp only [he, sub_self, norm_zero] at hn
    linarith
  unfold minorArcGeometricBound
  rw [ite_eq_right hz]
  apply min_le_min_left
  apply (div_le_div_iff₀ hn (by positivity : 0 < 2 * ‖(α : UnitAddCircle)‖)).mpr
  nlinarith

end TwoPointCorrelations

end OAI
