import OAI.NumberTheory.CubicMoment.Estimates.SmallBLogScale
import OAI.NumberTheory.CubicMoment.Estimates.CorrectedBilinearScale
import Mathlib.Analysis.Complex.ExponentialBounds

namespace OAI

/-! Integer logarithmic exponents for the low-height localization.
These inequalities let the cell width be chosen before the error saving. -/
noncomputable section
namespace CubicFirstMoment

lemma low_large_log {Z : ℝ} (hZ : (65536:ℝ)^2 ≤ Z) : 8 ≤ 1+Real.log Z := by
  have hz : (2:ℝ)^16 ≤ Z := by norm_num at *; linarith
  have hh := Real.log_le_log (by positivity : 0 < (2:ℝ)^16) hz
  rw [Real.log_pow] at hh
  have htwo := Real.log_two_gt_d9
  norm_num only [Nat.cast_ofNat] at hh
  linarith

lemma low_outer_log_root {A Z L : ℝ} (hA : 0 ≤ A) (hZ : 0 < Z) (hL : 0 < L)
    (a : ℕ) (hbound : A ≤ Z^2*L^(3*a)) :
    A^(1/3:ℝ) ≤ Z^(2/3:ℝ)*L^a := by
  have h := Real.rpow_le_rpow hA hbound (show (0:ℝ) ≤ 1/3 by norm_num)
  have hnum : (Z^2)^(1/3:ℝ) = Z^(2/3:ℝ) := by
    rw [←Real.rpow_natCast Z 2,←Real.rpow_mul hZ.le]
    norm_num
  have hden : (L^(3*a))^(1/3:ℝ) = L^a := by
    rw [←Real.rpow_natCast L (3*a),←Real.rpow_mul hL.le]
    push_cast
    rw [show (3*(a:ℝ))*(1/3:ℝ) = (a:ℝ) by ring,Real.rpow_natCast]
  rwa [Real.mul_rpow (sq_nonneg Z) (pow_nonneg hL.le _),hnum,hden] at h

lemma low_diagonal_log_scale {A Z L : ℝ} (hA : 0 < A) (hZ : 0 < Z) (hL : 0 < L)
    (k d a : ℕ) (hbound : A ≤ Z^2*L^(3*a)) :
    A*Z*L^d/L^(a+k+d) ≤ A^(2/3:ℝ)*Z^(5/3:ℝ)/L^k := by
  have hr := low_outer_log_root hA.le hZ hL a hbound
  have ha : A^(2/3:ℝ)*A^(1/3:ℝ) = A := by
    rw [←Real.rpow_add hA]
    norm_num
  have hz : Z*Z^(2/3:ℝ) = Z^(5/3:ℝ) := by
    nth_rw 1 [←Real.rpow_one Z]
    rw [←Real.rpow_add hZ]
    norm_num
  calc
    _ = A^(2/3:ℝ)*Z*A^(1/3:ℝ)*L^d/L^(a+k+d) := by
      rw [mul_right_comm (A^(2/3:ℝ)),ha]
    _ ≤ A^(2/3:ℝ)*Z*(Z^(2/3:ℝ)*L^a)*L^d/L^(a+k+d) := by gcongr
    _ = _ := by
      rw [pow_add,pow_add]
      field_simp
      rw [←hz]

lemma low_remainder_log_scale {L A Z M : ℝ} (hL : L ≠ 0)
    (d D k : ℕ) :
    (L^D)^4*((L^D)^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^(D*(d+4)+k)) =
      M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^k := by
  rw [pow_add,←pow_mul,←pow_mul]
  rw [Nat.mul_add,pow_add]
  field_simp

end CubicFirstMoment

end

end OAI
