import Mathlib

namespace OAI

section
noncomputable section
open scoped ENNReal

namespace CriticalPercolation

lemma geometric_fourth_bound (I : ℝ≥0∞) (A : ℝ) (hA : 0≤A) (n : ℕ)
    (h : I^4≤ENNReal.ofReal (A/(16:ℝ)^n)) :
    I≤ENNReal.ofReal ((A+1)*(1/2:ℝ)^n) := by
  apply (ENNReal.pow_le_pow_left_iff (by decide : 4≠0)).mp
  rw [←ENNReal.ofReal_pow (by positivity)]
  apply h.trans (ENNReal.ofReal_le_ofReal _)
  have hpow : ((1/2:ℝ)^n)^4 = (1/16:ℝ)^n := by
    rw [←pow_mul,Nat.mul_comm n 4,pow_mul]
    norm_num
  rw [mul_pow,hpow,one_div_pow,mul_one_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hsq : A≤(A+1)^2 := by nlinarith
  have ht : 1≤(A+1)^2 := by nlinarith
  nlinarith [sq_nonneg ((A+1)^2-1)]

end CriticalPercolation
end
end

end OAI
