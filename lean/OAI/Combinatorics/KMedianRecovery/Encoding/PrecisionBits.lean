import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.FirstSize

namespace OAI

namespace MetricKMedianRecovery.RadiusMenus

lemma menuWeight_uniform_lower (M E J : ℕ) (hM : 0 < M) (hJ : 0 < J)
    (e : Fin M ⊕ (Fin (E+1) ⊕ Fin J)) :
    1 / (3*((M:ℝ)+E+1)*2^J) ≤ menuWeight M E J e := by
  have hM0 : (0:ℝ) < M := by exact_mod_cast hM
  have hQ : (0:ℝ) < (M:ℝ)+E+1 := by positivity
  have hpow : (1:ℝ) ≤ 2^J := one_le_pow₀ (by norm_num)
  rcases e with i | (i | i)
  · simp only [menuWeight]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  · simp only [menuWeight]
    apply one_div_le_one_div_of_le (by positivity)
    have hE : (0:ℝ) ≤ E := by positivity
    nlinarith
  · simp only [menuWeight]
    have hi : i.val+1 ≤ J := i.isLt
    have hp : (1/2:ℝ)^J ≤ (1/2:ℝ)^(i.val+1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hi
    have ht := thirdNormalizer_pos hJ
    have ht1 := (thirdNormalizer_lt_one J).le
    have hu : (1/2:ℝ)^J ≤ (1/2:ℝ)^(i.val+1)/thirdNormalizer J := by
      apply (le_div_iff₀ ht).mpr
      exact (mul_le_of_le_one_right (by positivity) ht1).trans hp
    calc
      1/(3*((M:ℝ)+E+1)*2^J) = (1/(3*((M:ℝ)+E+1)))*(1/2:ℝ)^J := by
        rw [one_div_pow]
        simp only [one_div,mul_inv_rev]
        ring
      _ ≤ (1/3:ℝ)*(1/2:ℝ)^J := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply one_div_le_one_div_of_le (by norm_num)
        have hsum : (1:ℝ) ≤ (M:ℝ)+E+1 := by linarith [Nat.cast_nonneg (α := ℝ) M, Nat.cast_nonneg (α := ℝ) E]
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hu (by norm_num)

def precisionBits (n d M E J : ℕ) : ℕ := n+d+M+E+J+5

lemma precision_power (n d M E J : ℕ) :
    12*(n:ℝ)*d*((M:ℝ)+E+1)*2^J ≤ (2:ℝ)^(precisionBits n d M E J) := by
  have hn : (n:ℝ) ≤ (2:ℝ)^n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  have hd : (d:ℝ) ≤ (2:ℝ)^d := by exact_mod_cast (Nat.lt_two_pow_self (n := d)).le
  have hq : (M:ℝ)+E+1 ≤ (2:ℝ)^(M+E+1) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := M+E+1)).le
  calc
    12*(n:ℝ)*d*((M:ℝ)+E+1)*2^J ≤ 16*(2:ℝ)^n*2^d*2^(M+E+1)*2^J := by
      gcongr
      norm_num
    _ = (2:ℝ)^(precisionBits n d M E J) := by
      simp only [precisionBits,pow_add,pow_one]
      ring

end MetricKMedianRecovery.RadiusMenus

end OAI
