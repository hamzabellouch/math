import OAI.NumberTheory.TwoPoint.Halasz.HalaszCubicMaximum

namespace OAI

/-! The displacement of the weak strip has bounded cubic cost. -/
namespace TwoPointCorrelations

lemma halasz_weak_strip_cost {δ L : ℝ} (hδ : 0≤δ) (hL : 0<L)
    (hδhi : δ≤4*L^(-(2/3:ℝ))) :
    δ^(3/2:ℝ)*L≤(4:ℝ)^(3/2:ℝ) := by
  calc
    _ ≤ (4*L^(-(2/3:ℝ)))^(3/2:ℝ)*L := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hδ hδhi (by norm_num)) hL.le
    _ = _ := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hL.le _),
        ← Real.rpow_mul hL.le]
      norm_num only [show (-(2/3:ℝ))*(3/2)=-1 by norm_num,Real.rpow_neg_one]
      field_simp

lemma halasz_dyadic_log (k : ℕ) : Real.log ((2^k:ℕ):ℝ)=(k:ℝ)*Real.log 2 := by
  push_cast
  rw [Real.log_pow]

lemma halasz_dyadic_size {k : ℕ} (hk : 3≤k) :
    1≤Real.log ((2^k:ℕ):ℝ) ∧
      ((2^k:ℕ):ℝ)^(2/3:ℝ)≤((2^k:ℕ):ℝ)/2 := by
  have hkR : (3:ℝ)≤k := by exact_mod_cast hk
  have hlog2 : (1/2:ℝ)≤Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh ⊢
    exact hh
  refine ⟨?_,?_⟩
  · rw [halasz_dyadic_log]
    nlinarith
  · have hp : ((2^k:ℕ):ℝ)=(2:ℝ)^(k:ℝ) := by rw [Real.rpow_natCast]; push_cast; rfl
    rw [hp,← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    have he : (k:ℝ)*(2/3)≤(k:ℝ)-1 := by linarith
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) he
    simpa only [Real.rpow_sub (by norm_num : (0:ℝ)<2),Real.rpow_one] using hh

end TwoPointCorrelations

end OAI
