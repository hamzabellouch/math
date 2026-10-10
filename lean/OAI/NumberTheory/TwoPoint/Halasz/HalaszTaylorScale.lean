import OAI.NumberTheory.TwoPoint.Halasz.HalaszShortScale

namespace OAI

/-! Taylor remainder at the chosen short-variable scale. -/
namespace TwoPointCorrelations

lemma halasz_taylor_scale {M k : ℕ} {N x t α lam : ℝ}
    (hN : 1≤N) (hx : N≤x) (hM : (M:ℝ)^2≤N^(2*α)) (ht : |t|=N^lam)
    (hexp : lam+(2*α-1)*((k:ℝ)+1)≤-(1/2:ℝ)) :
    2*|t| * ((M:ℝ)^2/x)^(k+1)≤2*N^(-(1/2:ℝ)) := by
  have hN0 : 0<N := by linarith
  have hx0 : 0<x := hN0.trans_le hx
  have hquot : (M:ℝ)^2/x≤N^(2*α-1) := by
    calc
      _ ≤ N^(2*α)/x := div_le_div_of_nonneg_right hM hx0.le
      _ ≤ N^(2*α)/N := div_le_div_of_nonneg_left
        (Real.rpow_nonneg hN0.le _) hN0 hx
      _ = _ := by rw [Real.rpow_sub hN0,Real.rpow_one]
  have hp := pow_le_pow_left₀ (by positivity : 0≤(M:ℝ)^2/x) hquot (k+1)
  calc
    _ ≤ 2*|t| * (N^(2*α-1))^(k+1) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = 2*N^(lam+(2*α-1)*((k:ℝ)+1)) := by
      rw [ht,← Real.rpow_natCast,← Real.rpow_mul hN0.le]
      push_cast
      rw [Real.rpow_add hN0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN hexp) (by norm_num)

end TwoPointCorrelations

end OAI
