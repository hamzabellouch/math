import OAI.NumberTheory.JointDickman.Counting.UnitBinEnergy

namespace OAI

/-! # Exact normalization under a fixed dilation of short windows -/
namespace JointDickman
open MeasureTheory

theorem normalized_dilate_energy (f : ℝ → ℂ) (c : ℝ) {D X : ℝ} (hD : 0 < D) (hX : 0 < X) :
    (1/X)*(∫ z in X..2*X, ‖(c : ℂ)*f (z/D)‖^2) =
      c^2*((1/(X/D))*(∫ z in (X/D)..2*(X/D), ‖f z‖^2)) := by
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_div (fun y => ‖f y‖^2) hD.ne']
  simp only [smul_eq_mul]
  rw [show 2*X/D = 2*(X/D) by ring]
  field_simp

end JointDickman

end OAI
