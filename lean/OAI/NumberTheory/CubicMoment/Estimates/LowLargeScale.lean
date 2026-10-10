import OAI.NumberTheory.CubicMoment.Estimates.LowHeightLogScale

namespace OAI
noncomputable section
namespace CubicFirstMoment

lemma low_large_common_log_scale (j : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ Z : ℝ, 2 ≤ Z →
      (Z/2)^(2/3-1/8000:ℝ)*Z ≤ D*Z^(5/3:ℝ)/(1+Real.log Z)^j := by
  obtain ⟨D,hD,hlog⟩ := log_power_normalization_bound j
    (by norm_num : (0:ℝ) < 1/8000)
  refine ⟨D+1,by positivity,?_⟩
  intro Z hZ
  have hZp : 0 < Z := by linarith
  have hZ1 : 1 ≤ Z := by linarith
  have hL : 0 < 1+Real.log Z := by linarith [Real.log_nonneg hZ1]
  have hh := rpow_log_saving hZp hL j 0
    (p := 5/3) (s := 1/8000) (by simpa using hlog Z hZ1)
  simp only [pow_zero,mul_one] at hh
  calc
    _ ≤ Z^(2/3-1/8000:ℝ)*Z := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)) hZp.le
    _ = Z^(5/3-1/8000:ℝ) := by
      nth_rw 2 [←Real.rpow_one Z]
      rw [←Real.rpow_add hZp]
      congr 1
      norm_num
    _ ≤ D*Z^(5/3:ℝ)/(1+Real.log Z)^j := hh
    _ ≤ _ := by gcongr; linarith

end CubicFirstMoment

end

end OAI
