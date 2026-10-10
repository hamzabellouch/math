import Mathlib.Algebra.Order.Round
import OAI.NumberTheory.Ostmann.QuadraticCenter.RealQuadraticPhase

namespace OAI

/-! # Distance to the nearest integer controls a linear phase sum -/

namespace Ostmann

open scoped BigOperators

@[simp] theorem realAdditivePhase_intCast (k : ℤ) : realAdditivePhase k = 1 := by
  unfold realAdditivePhase
  convert Complex.exp_int_mul_two_pi_mul_I k using 1
  congr 1
  push_cast
  ring

theorem realAdditivePhase_sub_int (x : ℝ) (k : ℤ) :
    realAdditivePhase (x - k) = realAdditivePhase x := by
  rw [realAdditivePhase_sub, realAdditivePhase_intCast]
  simp

theorem norm_realAdditivePhase_sub_one (x : ℝ) :
    ‖realAdditivePhase x - 1‖ = 2 * |Real.sin (Real.pi * x)| := by
  unfold realAdditivePhase
  rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2 * Real.pi * x) / 2 = Real.pi * x by ring]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

theorem round_distance_le_phase_norm (x : ℝ) :
    4 * |x - (round x : ℤ)| ≤ ‖realAdditivePhase x - 1‖ := by
  rw [← realAdditivePhase_sub_int x (round x), norm_realAdditivePhase_sub_one]
  have hx := abs_sub_round x
  have hpi := Real.pi_pos
  have harg : |Real.pi * (x - (round x : ℤ))| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos hpi]
    nlinarith
  have hsin := Real.mul_abs_le_abs_sin harg
  rw [abs_mul, abs_of_pos hpi] at hsin
  have heq : 2 / Real.pi * (Real.pi * |x - (round x : ℤ)|) =
      2 * |x - (round x : ℤ)| := by field_simp
  rw [heq] at hsin
  linarith

theorem linear_phase_sum_bound (x : ℝ) (N : ℕ)
    (hx : 0 < |x - (round x : ℤ)|) :
    ‖∑ j ∈ Finset.range N, realAdditivePhase x ^ j‖ ≤
      min (N : ℝ) (1 / (2 * |x - (round x : ℤ)|)) := by
  have hnorm := round_distance_le_phase_norm x
  have hz : realAdditivePhase x ≠ 1 := by
    intro heq
    rw [heq, sub_self, norm_zero] at hnorm
    linarith
  have hb := norm_geometric_sum_le (realAdditivePhase x) N (norm_realAdditivePhase x) hz
  apply hb.trans
  apply min_le_min_left
  have hd : 0 < 4 * |x - (round x : ℤ)| := by positivity
  calc
    2 / ‖realAdditivePhase x - 1‖ ≤ 2 / (4 * |x - (round x : ℤ)|) :=
      div_le_div_of_nonneg_left (by norm_num) hd hnorm
    _ = 1 / (2 * |x - (round x : ℤ)|) := by ring

/-- The multiplicative form remains valid at integral phases, so no division
by zero or exceptional phase needs to enter the packing argument. -/
theorem linear_phase_sum_distance_bound (x : ℝ) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, realAdditivePhase x ^ j‖ ≤ N ∧
      2 * |x - (round x : ℤ)| *
        ‖∑ j ∈ Finset.range N, realAdditivePhase x ^ j‖ ≤ 1 := by
  have hz := norm_realAdditivePhase x
  constructor
  · calc
      _ ≤ ∑ j ∈ Finset.range N, ‖realAdditivePhase x ^ j‖ := norm_sum_le _ _
      _ = N := by simp [hz]
  · have hgeom := geom_sum_mul (realAdditivePhase x) N
    have heq : ‖∑ j ∈ Finset.range N, realAdditivePhase x ^ j‖ *
        ‖realAdditivePhase x - 1‖ = ‖realAdditivePhase x ^ N - 1‖ := by
      rw [← Complex.norm_mul, hgeom]
    have hb : ‖realAdditivePhase x ^ N - 1‖ ≤ 2 := by
      calc
        _ ≤ ‖realAdditivePhase x ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by norm_num [hz]
    have hm := mul_le_mul_of_nonneg_right (round_distance_le_phase_norm x)
      (norm_nonneg (∑ j ∈ Finset.range N, realAdditivePhase x ^ j))
    nlinarith

end Ostmann

end OAI
