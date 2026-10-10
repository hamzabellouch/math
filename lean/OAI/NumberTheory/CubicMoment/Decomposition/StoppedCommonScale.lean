import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCommonPointwise

namespace OAI

/-! A small square divisor is absorbed by the genuine size of a nonunit
common factor.  The condition is arithmetic roughness, not cancellation. -/
noncomputable section
namespace CubicFirstMoment

lemma square_divisor_common_outer_scale {Z A r m D : ℝ}
    (hZ : 0 ≤ Z) (hr : 0 < r) (hm : 0 < m) (hmr : m ≤ r)
    (hD : 0 < D) (hDr : D^4 ≤ r) (hA : Z^(3/2:ℝ) ≤ A) :
    (Z/r)^(3/2:ℝ) ≤ (A/D^2)/m := by
  have hDroot : D^2 ≤ Real.sqrt r := by
    nlinarith [Real.sq_sqrt hr.le,Real.sqrt_nonneg r,sq_nonneg (D^2)]
  have hden : D^2*m ≤ r^(3/2:ℝ) := by
    calc
      _ ≤ Real.sqrt r*r := mul_le_mul hDroot hmr hm.le (Real.sqrt_nonneg r)
      _ = _ := by
        rw [Real.sqrt_eq_rpow]
        calc
          r^(1/2:ℝ)*r = r^(1/2:ℝ)*r^(1:ℝ) := by rw [Real.rpow_one]
          _ = r^((1/2:ℝ)+1) := (Real.rpow_add hr _ _).symm
          _ = _ := by norm_num
  calc
    _ = Z^(3/2:ℝ)/r^(3/2:ℝ) := Real.div_rpow hZ hr.le _
    _ ≤ Z^(3/2:ℝ)/(D^2*m) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hZ _) (by positivity) hden
    _ ≤ A/(D^2*m) := div_le_div_of_nonneg_right hA (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
