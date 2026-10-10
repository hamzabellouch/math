import OAI.NumberTheory.Ostmann.QuadraticCenter.NumericCommonCenterBasic

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter

theorem kernelCoefficient_population_ratio_le {J J₀ Z : ℝ} {k : ℕ}
    (hJ : 0 < J) (hJ₀ : 1 ≤ J₀) (hZ : 1 ≤ Z)
    (hcenter : J^k*Z^(-(7/50 : ℝ))/4 ≤ 2*J*J₀^(k-1)) :
    J^k/J₀^k ≤ 8*J*Z := by
  have hZp : 0 < Z := by linarith
  have hJ₀p : 0 < J₀ := by linarith
  have hfrac : J^k/(4*Z^(7/50 : ℝ)) ≤ 2*J*J₀^(k-1) := by
    simpa only [Real.rpow_neg hZp.le, div_eq_mul_inv, mul_inv_rev, mul_assoc] using hcenter
  have hh := (div_le_iff₀ (by positivity : 0 < 4*Z^(7/50 : ℝ))).mp hfrac
  have hp := pow_le_pow_right₀ hJ₀ (Nat.sub_le k 1)
  have hzpow : Z^(7/50 : ℝ) ≤ Z := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hZ (by norm_num : (7/50 : ℝ) ≤ 1)
  apply (div_le_iff₀ (pow_pos hJ₀p k)).mpr
  calc
    J^k ≤ (2*J*J₀^(k-1))*(4*Z^(7/50 : ℝ)) := hh
    _ ≤ (2*J*J₀^k)*(4*Z) := mul_le_mul
      (mul_le_mul_of_nonneg_left hp (by positivity))
      (mul_le_mul_of_nonneg_left hzpow (by norm_num)) (by positivity) (by positivity)
    _ = _ := by ring

theorem kernelCoefficient_budget_le {J J₀ Z δ : ℝ} {k : ℕ}
    (hJ : 0 < J) (hJ₀ : 1 ≤ J₀) (hZ : 1 ≤ Z) (hδ : 0 < δ)
    (hJu : J ≤ 2*Z)
    (hcenter : J^k*Z^(-(7/50 : ℝ))/4 ≤ 2*J*J₀^(k-1)) :
    (2*Z)^k*((k.factorial : ℝ)/J₀^k)*(2/δ^k)^2 ≤
      64*Z^2*(2*Z*(k : ℝ)/(J*δ^2))^k := by
  have hJ₀p : 0 < J₀ := by linarith
  have hz : 0 < Z := by linarith
  have hratio := kernelCoefficient_population_ratio_le hJ hJ₀ hZ hcenter
  have hf : (k.factorial : ℝ) ≤ (k : ℝ)^k := by exact_mod_cast Nat.factorial_le_pow k
  calc
    _ = 4*(J^k/J₀^k)*(k.factorial : ℝ)*(2*Z/(J*δ^2))^k := by
      simp only [div_pow, mul_pow]
      field_simp
      ring
    _ ≤ 4*(8*J*Z)*(k : ℝ)^k*(2*Z/(J*δ^2))^k := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_left hratio (by norm_num)) hf
          (by positivity) (by positivity)) (by positivity)
    _ = 32*J*Z*(2*Z*(k : ℝ)/(J*δ^2))^k := by
      rw [mul_assoc (4*(8*J*Z)), ←mul_pow]
      congr 1 <;> ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith [mul_le_mul_of_nonneg_right hJu hz.le]

end Ostmann.QuadraticCenter

end

end OAI
