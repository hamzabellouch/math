import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCubeScale

namespace OAI

/-! Explicit logarithmic choices for the full stopped product Mellin line. -/
noncomputable section
namespace CubicFirstMoment

lemma stopped_product_window_power {L t : ℝ} (hL : 2 ≤ L) (ht0 : 0 ≤ t) (ht : t ≤ L)
    (Ct s : ℕ) (hs : 2*Ct ≤ s) : (1+t)^Ct ≤ L^s := by
  calc
    _ ≤ (2*L)^Ct := pow_le_pow_left₀ (by linarith) (by linarith) Ct
    _ = 2^Ct*L^Ct := mul_pow _ _ _
    _ ≤ L^Ct*L^Ct := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num) hL Ct) (pow_nonneg (by linarith) _)
    _ = L^(2*Ct) := by rw [←pow_add]; congr 1; omega
    _ ≤ L^s := pow_le_pow_right₀ (by linarith) hs

lemma stopped_product_shift_power {L u τ : ℝ} (hL : 2 ≤ L)
    (H s : ℕ) (hu : |u| ≤ L^H) (hτ : |τ| ≤ (4/3)*L^s) :
    |u-τ| ≤ L^(H+s+2) := by
  have hL1 : 1 ≤ L := by linarith
  have hLH : L^H ≤ L^(H+s) := pow_le_pow_right₀ hL1 (by omega)
  have hLs : L^s ≤ L^(H+s) := pow_le_pow_right₀ hL1 (by omega)
  have hbase : 0 ≤ L^(H+s) := pow_nonneg (by linarith : 0 ≤ L) _
  calc
    _ ≤ |u|+|τ| := abs_sub _ _
    _ ≤ L^H+(4/3)*L^s := add_le_add hu hτ
    _ ≤ 3*L^(H+s) := by nlinarith
    _ = L^(H+s)*3 := by ring
    _ ≤ L^(H+s)*L^2 := mul_le_mul_of_nonneg_left
      (by nlinarith [sq_nonneg (L-2)] : (3:ℝ) ≤ L^2) hbase
    _ = _ := (pow_add _ _ _).symm

lemma stopped_product_model_scale {A b X : ℝ} (hA1 : 1 ≤ A) (hb : 1 ≤ b)
    (hX : Real.exp 1 ≤ X) (hbX : b ≤ X) (hAb : A ≤ b^2) (d : ℕ) :
    (2*(A*b))*(A*b/2)^(-1/6:ℝ)*(1+Real.log (2*(A*b)))^d ≤
      (4*5^d)*(A^(5/6:ℝ)*b^(5/6:ℝ))*(Real.log X)^d := by
  have hA : 0 < A := zero_lt_one.trans_le hA1
  have hbp : 0 < b := zero_lt_one.trans_le hb
  have hXp : 0 < X := (Real.exp_pos 1).trans_le hX
  have hL : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hlogb : Real.log b ≤ Real.log X := Real.log_le_log hbp hbX
  have hlogA : Real.log A ≤ 2*Real.log X := by
    have hh := Real.log_le_log hA hAb
    rw [Real.log_pow] at hh
    norm_num at hh
    linarith
  have hlog : 1+Real.log (2*(A*b)) ≤ 5*Real.log X := by
    rw [Real.log_mul (by norm_num) (mul_pos hA hbp).ne',Real.log_mul hA.ne' hbp.ne']
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at htwo
    linarith
  have hscale : (2*(A*b))*(A*b/2)^(-1/6:ℝ) ≤
      4*(A^(5/6:ℝ)*b^(5/6:ℝ)) := by
    rw [Real.div_rpow (mul_pos hA hbp).le (by norm_num),div_eq_mul_inv,
      ←Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    have hid : (A*b)*(A*b)^(-1/6:ℝ) = A^(5/6:ℝ)*b^(5/6:ℝ) := by
      nth_rw 1 [←Real.rpow_one (A*b)]
      rw [←Real.rpow_add (mul_pos hA hbp)]
      norm_num
      exact Real.mul_rpow hA.le hbp.le
    have ht : (2:ℝ)^(1/6:ℝ) ≤ 2 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1:ℝ) ≤ 2) (by norm_num : (1/6:ℝ) ≤ 1)
    have he : -(-1/6:ℝ) = 1/6 := by ring
    rw [he]
    calc
      _ = 2*((A*b)*(A*b)^(-1/6:ℝ))*(2:ℝ)^(1/6:ℝ) := by ring
      _ = 2*(A^(5/6:ℝ)*b^(5/6:ℝ))*(2:ℝ)^(1/6:ℝ) := by rw [hid]
      _ ≤ 2*(A^(5/6:ℝ)*b^(5/6:ℝ))*2 :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _ = _ := by ring
  have hlower : 0 ≤ 1+Real.log (2*(A*b)) := by
    have hab : 1 ≤ A*b := one_le_mul_of_one_le_of_one_le hA1 hb
    have hh := Real.log_nonneg (by linarith : 1 ≤ 2*(A*b))
    linarith
  calc
    _ ≤ (4*(A^(5/6:ℝ)*b^(5/6:ℝ)))*(5*Real.log X)^d :=
      mul_le_mul hscale (pow_le_pow_left₀ hlower hlog d)
        (pow_nonneg hlower _) (by positivity)
    _ = _ := by rw [mul_pow]; ring

lemma stopped_product_power_absorb {L B K : ℝ} (hL : 1 ≤ L) (hB : 0 ≤ B)
    (hK : 0 ≤ K) (d k s : ℕ) (hs : d+k ≤ s) :
    K*B*L^d/L^s ≤ K*B/L^k := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  apply (div_le_div_iff₀ (pow_pos hLp s) (pow_pos hLp k)).mpr
  calc
    _ = K*B*L^(d+k) := by rw [pow_add]; ring
    _ ≤ K*B*L^s := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hs) (mul_nonneg hK hB)

end CubicFirstMoment

end

end OAI
