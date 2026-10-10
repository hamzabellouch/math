import OAI.NumberTheory.CubicMoment.Estimates.LogarithmicWeightFamily

namespace OAI

/-! The sparse beta energy beats both the logarithmic alpha energy and
any fixed product-support dilation in the cubic bilinear sieve. -/
noncomputable section
namespace CubicFirstMoment

lemma sparse_bilinear_shape {X A B M : ℝ} (hX : 1 ≤ X)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 1 ≤ M)
    (hAX : A ≤ M*X^(2/3:ℝ)) (hBX : B ≤ M*X^(2/3:ℝ))
    (hAB : A*B ≤ M*X) :
    A+B+(A*B)^(2/3:ℝ) ≤ 3*M*X^(2/3:ℝ) := by
  have hp : M^(2/3:ℝ) ≤ M := by
    calc
      _ ≤ M^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hM (by norm_num)
      _ = M := Real.rpow_one _
  have hb : (A*B)^(2/3:ℝ) ≤ M*X^(2/3:ℝ) := by
    calc
      _ ≤ (M*X)^(2/3:ℝ) := Real.rpow_le_rpow (mul_nonneg hA hB) hAB (by norm_num)
      _ = M^(2/3:ℝ)*X^(2/3:ℝ) := Real.mul_rpow (by linarith) (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg (by linarith) _)
  linarith

lemma sparse_bilinear_power_bound {X A B M δ H Kα Kβ : ℝ}
    (hX : 1 ≤ X) (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 1 ≤ M)
    (hδ : 0 < δ) (_hH : 0 ≤ H) (hKα : 0 ≤ Kα) (hKβ : 0 ≤ Kβ)
    (d : ℕ) (hAX : A ≤ M*X^(2/3:ℝ)) (hBX : B ≤ M*X^(2/3:ℝ))
    (hAB : A*B ≤ M*X)
    (hlog : X^(-(δ/4))*(1+Real.log X)^d ≤ H) :
    (A*B)^(δ/4)*(A+B+(A*B)^(2/3:ℝ))*
        (Kα*A*(1+Real.log X)^d)*(Kβ*B*X^(-δ)) ≤
      (3*Kα*Kβ*H*M^(2+δ/4))*X^(5/3-δ/2) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hMp : 0 < M := zero_lt_one.trans_le hM
  have hpref : (A*B)^(δ/4) ≤ M^(δ/4)*X^(δ/4) := by
    simpa only [Real.mul_rpow hMp.le hXp.le] using
      Real.rpow_le_rpow (mul_nonneg hA hB) hAB (by positivity : 0 ≤ δ/4)
  have hshape := sparse_bilinear_shape hX hA hB hM hAX hBX hAB
  have hlog' : (1+Real.log X)^d ≤ H*X^(δ/4) := by
    have hh := mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hXp.le (δ/4))
    have he : X^(-(δ/4))*X^(δ/4) = 1 := by
      rw [←Real.rpow_add hXp]
      simp
    calc
      (1+Real.log X)^d = (X^(-(δ/4))*X^(δ/4))*(1+Real.log X)^d := by rw [he,one_mul]
      _ = X^(-(δ/4))*(1+Real.log X)^d*X^(δ/4) := by ring
      _ ≤ _ := hh
  have hL : 0 ≤ (1+Real.log X)^d := pow_nonneg (by linarith [Real.log_nonneg hX]) _
  have hbig :
      (A*B)^(δ/4)*(A+B+(A*B)^(2/3:ℝ))*(A*B)*(1+Real.log X)^d*X^(-δ) ≤
      (M^(δ/4)*X^(δ/4))*(3*M*X^(2/3:ℝ))*(M*X)*(H*X^(δ/4))*X^(-δ) := by
    gcongr
  have hpow : X^(δ/4)*X^(2/3:ℝ)*X*X^(δ/4)*X^(-δ) = X^(5/3-δ/2) := by
    nth_rw 3 [←Real.rpow_one X]
    rw [←Real.rpow_add hXp,←Real.rpow_add hXp,←Real.rpow_add hXp,←Real.rpow_add hXp]
    congr 1
    ring
  have hm : M^(δ/4)*M*M = M^(2+δ/4) := by
    nth_rw 2 [←Real.rpow_one M]
    nth_rw 3 [←Real.rpow_one M]
    rw [←Real.rpow_add hMp,←Real.rpow_add hMp]
    congr 1
    ring
  calc
    _ = (Kα*Kβ)*((A*B)^(δ/4)*(A+B+(A*B)^(2/3:ℝ))*(A*B)*
        (1+Real.log X)^d*X^(-δ)) := by ring
    _ ≤ (Kα*Kβ)*((M^(δ/4)*X^(δ/4))*(3*M*X^(2/3:ℝ))*(M*X)*
        (H*X^(δ/4))*X^(-δ)) := mul_le_mul_of_nonneg_left hbig (mul_nonneg hKα hKβ)
    _ = (3*Kα*Kβ*H)*(M^(δ/4)*M*M)*
        (X^(δ/4)*X^(2/3:ℝ)*X*X^(δ/4)*X^(-δ)) := by ring
    _ = _ := by rw [hm,hpow]

end CubicFirstMoment

end

end OAI
