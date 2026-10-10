import OAI.NumberTheory.CubicMoment.Estimates.SmallBCommonScale
import OAI.NumberTheory.CubicMoment.Estimates.LogarithmicWeightFamily

namespace OAI

/-! Explicit outer-length and logarithmic losses for the small-B
variance. Only positive real powers and the proved logarithm bound occur. -/
noncomputable section
namespace CubicFirstMoment

lemma smallB_outer_log_root {A Z L : ℝ} (hA : 0 ≤ A) (hZ : 0 < Z) (hL : 0 < L)
    (m : ℕ) (hbound : A ≤ Z^2/L^(3*m)) :
    A^(1/3:ℝ) ≤ Z^(2/3:ℝ)/L^m := by
  have h := Real.rpow_le_rpow hA hbound (show (0:ℝ) ≤ 1/3 by norm_num)
  have hnum : (Z^2)^(1/3:ℝ) = Z^(2/3:ℝ) := by
    rw [← Real.rpow_natCast Z 2,← Real.rpow_mul hZ.le]
    norm_num
  have hden : (L^(3*m))^(1/3:ℝ) = L^m := by
    rw [← Real.rpow_natCast L (3*m),← Real.rpow_mul hL.le]
    push_cast
    rw [show (3*(m:ℝ))*(1/3:ℝ) = (m:ℝ) by ring,Real.rpow_natCast]
  rwa [Real.div_rpow (sq_nonneg Z) (pow_nonneg hL.le _),hnum,hden] at h

lemma smallB_diagonal_log_scale {A Z L : ℝ} (hA : 0 < A) (hZ : 0 < Z) (hL : 0 < L)
    (k d : ℕ) (hbound : A ≤ Z^2/L^(3*(k+d))) :
    A*Z*L^d ≤ A^(2/3:ℝ)*Z^(5/3:ℝ)/L^k := by
  have hr := smallB_outer_log_root hA.le hZ hL (k+d) hbound
  have ha : A^(2/3:ℝ)*A^(1/3:ℝ) = A := by
    rw [← Real.rpow_add hA]
    norm_num
  have hz : Z*Z^(2/3:ℝ) = Z^(5/3:ℝ) := by
    nth_rw 1 [← Real.rpow_one Z]
    rw [← Real.rpow_add hZ]
    norm_num
  calc
    _ = A^(2/3:ℝ)*Z*A^(1/3:ℝ)*L^d := by rw [mul_right_comm (A^(2/3:ℝ)),ha]
    _ ≤ A^(2/3:ℝ)*Z*(Z^(2/3:ℝ)/L^(k+d))*L^d := by gcongr
    _ = _ := by
      rw [pow_add]
      field_simp
      rw [← hz]

lemma smallB_nondiagonal_log_scale {A Z L H δ : ℝ}
    (hA : 0 ≤ A) (hZ : 0 < Z) (hL : 0 < L) (k d : ℕ)
    (hbound : Z^(-δ)*L^(k+d) ≤ H) :
    A^(2/3:ℝ)*Z^(5/3-δ)*L^d ≤ H*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^k := by
  apply (le_div_iff₀ (pow_pos hL k)).mpr
  have hz : Z^(5/3-δ) = Z^(5/3:ℝ)*Z^(-δ) := by
    rw [← Real.rpow_add hZ]
    congr 1
  rw [hz]
  have hh := mul_le_mul_of_nonneg_left hbound
    (show 0 ≤ A^(2/3:ℝ)*Z^(5/3:ℝ) by positivity)
  rw [pow_add] at hh
  nlinarith only [hh]

end CubicFirstMoment

end

end OAI
