import OAI.Geometry.RCD.Heat.HeatActionBasepoint

namespace OAI

/-! # The centered action slope is proportional to the physical radius -/

open scoped NNReal
noncomputable section
namespace RegularPointCoordinates

theorem centered_action_radius_bound {K C R r δ : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hRr : R ≤ r) (hr : 0 < r) :
    3*Real.sqrt (Real.exp |K| * (16*C*(R+32*r)^2/(δ/2)^2)) ≤
      (3*Real.sqrt (Real.exp |K| * (16*C*33^2/(δ/2)^2)))*r := by
  have hbase : 0 ≤ Real.exp |K| * (16*C*33^2/(δ/2)^2) := by positivity
  have hsq : (R+32*r)^2 ≤ (33*r)^2 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hrad : Real.exp |K| * (16*C*(R+32*r)^2/(δ/2)^2) ≤
      (Real.exp |K| * (16*C*33^2/(δ/2)^2))*r^2 := by
    calc
      _ ≤ Real.exp |K| * (16*C*(33*r)^2/(δ/2)^2) := by
        gcongr
      _ = _ := by ring
  calc
    _ ≤ 3*Real.sqrt ((Real.exp |K| * (16*C*33^2/(δ/2)^2))*r^2) := by
      gcongr
    _ = _ := by rw [Real.sqrt_mul hbase,Real.sqrt_sq_eq_abs,abs_of_pos hr]; ring

end RegularPointCoordinates

end

end OAI
