import OAI.NumberTheory.CubicMoment.Estimates.PrimeConductorScale

namespace OAI

/-! The ordinary small-conductor bound becomes an arbitrary logarithmic
saving above an explicit logarithmic conductor threshold. -/
noncomputable section
namespace CubicFirstMoment

lemma ordinary_small_conductor_power {U V L : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hL : 0 ≤ L) (hsize : (U*V)^2 ≤ L) :
    (U*V)^(1/12:ℝ)*((U*V)^2+L)*L ≤
      2*L^2*(U*V^2)^(1/3:ℝ)*(U*V^2)^(-(1/4:ℝ)) := by
  have hUV : 0 < U*V := mul_pos (zero_lt_one.trans_le hU) (zero_lt_one.trans_le hV)
  have hD : 0 < U*V^2 := mul_pos (zero_lt_one.trans_le hU) (pow_pos (zero_lt_one.trans_le hV) _)
  have hcomp : U*V ≤ U*V^2 := mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
  have he : (U*V^2)^(1/3:ℝ)*(U*V^2)^(-(1/4:ℝ)) = (U*V^2)^(1/12:ℝ) := by
    rw [← Real.rpow_add hD]
    norm_num
  rw [mul_assoc (2*L^2),he]
  calc
    _ ≤ (U*V^2)^(1/12:ℝ)*(2*L)*L := mul_le_mul_of_nonneg_right
      (mul_le_mul (Real.rpow_le_rpow hUV.le hcomp (by norm_num)) (by linarith)
        (by positivity) (Real.rpow_nonneg hD.le _)) hL
    _ = _ := by ring

lemma conductor_log_tail {D z : ℝ} (hD : 0 < D) (hz : 1 ≤ z) (a k : ℕ)
    (hlarge : z^(4*(a+k)) ≤ D) :
    D^(-(1/4:ℝ))*z^a ≤ 1/z^k := by
  have hzp : 0 < z := zero_lt_one.trans_le hz
  have hp : z^(a+k) ≤ D^(1/4:ℝ) := by
    have hh := Real.rpow_le_rpow (pow_nonneg hzp.le (4*(a+k))) hlarge (by norm_num : (0:ℝ) ≤ 1/4)
    rw [← Real.rpow_natCast z (4*(a+k)),← Real.rpow_mul hzp.le] at hh
    have he : ((4*(a+k):ℕ):ℝ)*(1/4) = (a+k:ℕ) := by push_cast; ring
    rw [he,Real.rpow_natCast] at hh
    exact hh
  apply (le_div_iff₀ (pow_pos hzp k)).mpr
  rw [mul_assoc,← pow_add,Real.rpow_neg hD.le,inv_mul_eq_div]
  exact (div_le_one (Real.rpow_pos_of_pos hD _)).mpr hp

lemma ordinary_log_tail_bound {H C R J L U V z : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hJ : 0 ≤ J) (hL : 0 ≤ L)
    (hU : 1 ≤ U) (hV : 1 ≤ V) (hz : 1 ≤ z) (a k : ℕ)
    (hsize : (U*V)^2 ≤ L) (hlarge : z^(4*(a+k)) ≤ U*V^2)
    (hH : H ≤ C*R*J*(U*V)^(1/12:ℝ)*((U*V)^2+L)*L*z^a) :
    H ≤ (2*C)*R*J*L^2*(U*V^2)^(1/3:ℝ)/z^k := by
  have hD : 0 < U*V^2 := mul_pos (zero_lt_one.trans_le hU) (pow_pos (zero_lt_one.trans_le hV) _)
  have hp := ordinary_small_conductor_power hU hV hL hsize
  have ht := conductor_log_tail hD hz a k hlarge
  calc
    H ≤ (C*R*J)*((U*V)^(1/12:ℝ)*((U*V)^2+L)*L)*z^a := by convert hH using 1; ring
    _ ≤ (C*R*J)*(2*L^2*(U*V^2)^(1/3:ℝ)*(U*V^2)^(-(1/4:ℝ)))*z^a :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (pow_nonneg (by linarith) _)
    _ = ((2*C)*R*J*L^2*(U*V^2)^(1/3:ℝ))*((U*V^2)^(-(1/4:ℝ))*z^a) := by ring
    _ ≤ ((2*C)*R*J*L^2*(U*V^2)^(1/3:ℝ))*(1/z^k) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
