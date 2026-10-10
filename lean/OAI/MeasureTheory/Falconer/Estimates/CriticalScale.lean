import OAI.MeasureTheory.Falconer.Slicing.GaussianShellEnergy

namespace OAI

/-! # Exact cancellation at the half-dimensional frequency scale -/

namespace Falconer

theorem critical_gaussian_scale {B C : ℝ} (hB : 0 < B) (hC : 0 ≤ C) (s : ℝ) :
    (C*B^2)^s*(1/B)^s/B^s = C^s := by
  have hp : (B^2)^s = B^s*B^s := by
    rw [pow_two,Real.mul_rpow hB.le hB.le]
  rw [Real.mul_rpow hC (sq_nonneg B),hp,one_div,Real.inv_rpow hB.le]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hB s)]

theorem half_dimension_scale {d : ℕ} {B : ℝ} (hB : 0 < B) :
    (16*Real.pi*B^2)^((d:ℝ)/2)*(1/B)^((d:ℝ)/2)/B^((d:ℝ)/2) =
      (16*Real.pi)^((d:ℝ)/2) :=
  critical_gaussian_scale hB (by positivity) _

end Falconer

end OAI
