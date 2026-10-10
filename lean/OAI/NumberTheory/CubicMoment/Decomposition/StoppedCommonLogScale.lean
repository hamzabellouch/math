import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCubeScale

namespace OAI

/-! Logarithmic choices for the three proved common-factor remainder costs. -/
noncomputable section
namespace CubicFirstMoment

lemma stopped_common_rough_log_scale {b L R : ℝ} (hb : 1 ≤ b) (hL : 1 ≤ L)
    (hbL : Real.log b ≤ L) (j k : ℕ) (hR : L^(6*(j+k)) ≤ R) :
    (1+Real.log b)^j*R^(-(1/6:ℝ)) ≤ (2:ℝ)^j/L^k := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hRp : 0 < R := (pow_pos hLp _).trans_le hR
  have hp := Real.rpow_le_rpow_of_nonpos (pow_pos hLp (6*(j+k))) hR
    (show -(1/6:ℝ) ≤ 0 by norm_num)
  have hr : L^j*R^(-(1/6:ℝ)) ≤ 1/L^k := by
    apply (mul_le_mul_of_nonneg_left hp (pow_nonneg hLp.le _)).trans_eq
    rw [←Real.rpow_natCast L (6*(j+k)),←Real.rpow_mul hLp.le]
    have he : ((6*(j+k):ℕ):ℝ)*(-(1/6:ℝ)) = -((j+k:ℕ):ℝ) := by
      push_cast
      ring
    rw [he,Real.rpow_neg hLp.le,Real.rpow_natCast,pow_add]
    field_simp
  calc
    _ ≤ (2*L)^j*R^(-(1/6:ℝ)) := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by linarith [Real.log_nonneg hb]) (by linarith) j) (by positivity)
    _ = (2:ℝ)^j*(L^j*R^(-(1/6:ℝ))) := by rw [mul_pow]; ring
    _ ≤ (2:ℝ)^j*(1/L^k) := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := by ring

lemma stopped_common_error_scale {A b L R K M : ℝ} (hA : 0 < A)
    (hb : 1 ≤ b) (hL : 1 ≤ L) (hK : 0 ≤ K) (hbL : Real.log b ≤ L)
    (j k : ℕ) (hR : L^(6*(j+k)) ≤ R)
    (hpow : b^(-(1/32:ℝ)) ≤ 1/L^k) (hcut : A ≤ b^2/L^(3*k)) :
    K*(A^(2/3:ℝ)*b^(5/3:ℝ)*(1+Real.log b)^j*R^(-(1/6:ℝ))+
      A^(2/3:ℝ)*b^(5/3-1/32:ℝ)+A*b)*M^2 ≤
      K*((2:ℝ)^j+2)*A^(2/3:ℝ)*b^(5/3:ℝ)*M^2/L^k := by
  have hbp : 0 < b := zero_lt_one.trans_le hb
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hr := stopped_common_rough_log_scale hb hL hbL j k hR
  have he : b^(5/3-1/32:ℝ) = b^(5/3:ℝ)*b^(-(1/32:ℝ)) := by
    rw [←Real.rpow_add hbp]
    congr 1
  have hd : A*b ≤ A^(2/3:ℝ)*b^(5/3:ℝ)/L^k := by
    simpa only [zero_add,Nat.zero_add,pow_zero,mul_one] using
      cube_lattice_error_scale hA hbp hLp 0 k (by simpa using hcut)
  have hn : A^(2/3:ℝ)*b^(5/3-1/32:ℝ) ≤ A^(2/3:ℝ)*b^(5/3:ℝ)/L^k := by
    rw [he,←mul_assoc]
    exact (mul_le_mul_of_nonneg_left hpow (by positivity)).trans_eq (by ring)
  have hs : A^(2/3:ℝ)*b^(5/3:ℝ)*(1+Real.log b)^j*R^(-(1/6:ℝ)) ≤
      (2:ℝ)^j*(A^(2/3:ℝ)*b^(5/3:ℝ))/L^k := by
    calc
      _ = (A^(2/3:ℝ)*b^(5/3:ℝ))*((1+Real.log b)^j*R^(-(1/6:ℝ))) := by ring
      _ ≤ (A^(2/3:ℝ)*b^(5/3:ℝ))*((2:ℝ)^j/L^k) :=
        mul_le_mul_of_nonneg_left hr (by positivity)
      _ = _ := by ring
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hs hn) hd) hK) (sq_nonneg M)).trans_eq
      (by ring)

end CubicFirstMoment

end

end OAI
