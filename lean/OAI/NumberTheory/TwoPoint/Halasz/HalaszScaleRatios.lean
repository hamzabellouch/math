import OAI.NumberTheory.TwoPoint.Halasz.HalaszLogWeightBounds

namespace OAI

/-! Elementary scale ratios in the logarithmic coefficient weights. -/
namespace TwoPointCorrelations

lemma halasz_inverse_short_power {M : ℕ} (hM : 1≤M)
    {N α : ℝ} (hN : 0<N) (hscale : N^α≤2*(M:ℝ)) (d : ℕ) :
    1/(M:ℝ)^d≤(2:ℝ)^d*N^(-α*(d:ℝ)) := by
  have hM0 : 0<(M:ℝ) := by exact_mod_cast (show 0<M by omega)
  have hp : N^(α*(d:ℝ))≤(2:ℝ)^d*(M:ℝ)^d := by
    calc
      _ = (N^α)^d := by rw [← Real.rpow_natCast,← Real.rpow_mul hN.le]
      _ ≤ (2*(M:ℝ))^d := pow_le_pow_left₀ (Real.rpow_nonneg hN.le _) hscale d
      _ = _ := mul_pow _ _ _
  calc
    _ ≤ (2:ℝ)^d/N^(α*(d:ℝ)) := by
      apply (div_le_div_iff₀ (pow_pos hM0 d) (Real.rpow_pos_of_pos hN _)).mpr
      simpa only [one_mul] using hp
    _ = _ := by rw [show -α*(d:ℝ)= -(α*(d:ℝ)) by ring,Real.rpow_neg hN.le]; ring

lemma halasz_height_over_long_power {t z N lam : ℝ} (hN : 0<N)
    (hz : N≤z) (ht : |t|=N^lam) (d : ℕ) :
    |t|/z^d≤N^(lam-(d:ℝ)) := by
  have hz0 : 0<z := hN.trans_le hz
  calc
    _ ≤ |t|/N^d := div_le_div_of_nonneg_left (abs_nonneg t)
      (pow_pos hN d) (pow_le_pow_left₀ hN.le hz d)
    _ = _ := by rw [ht,Real.rpow_sub hN,Real.rpow_natCast]

lemma halasz_long_over_short_height {M : ℕ} (hM : 1≤M)
    {t z N α lam : ℝ} (hN : 0<N) (hz : 0≤z) (hzhi : z≤2*N)
    (ht : |t|=N^lam) (hscale : N^α≤2*(M:ℝ)) (d : ℕ) :
    z^d/(((M:ℝ)^d)^2*|t|)≤(8:ℝ)^d*N^((d:ℝ)-2*α*(d:ℝ)-lam) := by
  have hinv := halasz_inverse_short_power hM hN hscale d
  have hsq := pow_le_pow_left₀ (by positivity : 0≤1/(M:ℝ)^d) hinv 2
  have hzpow := pow_le_pow_left₀ hz hzhi d
  have hmult := mul_le_mul hzpow hsq (by positivity) (by positivity)
  have hmult' := mul_le_mul_of_nonneg_right hmult
    (Real.rpow_nonneg hN.le (-lam))
  calc
    _ = (z^d*(1/(M:ℝ)^d)^2)*N^(-lam) := by
      rw [ht,Real.rpow_neg hN.le]
      ring
    _ ≤ ((2*N)^d*((2:ℝ)^d*N^(-α*(d:ℝ)))^2)*N^(-lam) := hmult'
    _ = (8:ℝ)^d*N^((d:ℝ)-2*α*(d:ℝ)-lam) := by
      rw [mul_pow,mul_pow,← pow_mul,← Real.rpow_natCast N d,
        ← Real.rpow_natCast (N^(-α*(d:ℝ))) 2,← Real.rpow_mul hN.le]
      norm_num only [Nat.cast_ofNat]
      have he : (2:ℝ)^d*(2:ℝ)^(d*2)=(8:ℝ)^d := by
        rw [show d*2=2*d by omega,pow_mul,← mul_pow]
        norm_num
      calc
        _ = ((2:ℝ)^d*(2:ℝ)^(d*2))*(N^(d:ℝ)*N^((-α*(d:ℝ))*(2:ℝ))*N^(-lam)) := by ring
        _ = _ := by rw [he,← Real.rpow_add hN,← Real.rpow_add hN]; congr 2; ring

end TwoPointCorrelations

end OAI
