import OAI.MeasureTheory.Falconer.Recursion.ProfileNormalBudget

namespace OAI

/-! Common explicit bounds for the geometric constants of all selected
normal and good intervals. The exponent range needed here is only [0,2]. -/
namespace Falconer

theorem profile_geometry_costs {K i j B : ℕ} (hi : i ≤ K) (hj : j ≤ K)
    {t A W : ℝ} (_ht : 0 ≤ t) (ht2 : t ≤ 2) (hA : 0 ≤ A) (hW : 1 ≤ W) :
    (max 1 ((49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^t)*4^t)*
      (W*(2:ℝ)^(2*i+2*j))))*4^t ≤
        100000*W*(2:ℝ)^(6*K)*(2:ℝ)^A*(2:ℝ)^(2*B) ∧
    25*(49*((2:ℝ)^i*(2:ℝ)^(t*((B:ℝ)+3)+A))) ≤
        100000*W*(2:ℝ)^(6*K)*(2:ℝ)^A*(2:ℝ)^(2*B) := by
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have h4 : (4:ℝ)^t ≤ 16 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4) ht2
    norm_num only [Real.rpow_two] at hh
    exact hh
  have hB : ((2:ℝ)^B)^t ≤ (2:ℝ)^(2*B) := by
    have hh := Real.rpow_le_rpow_of_exponent_le
      (show (1:ℝ) ≤ (2:ℝ)^B from one_le_pow₀ (by norm_num)) ht2
    simpa only [Real.rpow_two,← pow_mul,Nat.mul_comm] using hh
  let D := W*(2:ℝ)^(6*K)*(2:ℝ)^A*(2:ℝ)^(2*B)
  have hD : 1 ≤ D := by
    apply one_le_mul_of_one_le_of_one_le
    · apply one_le_mul_of_one_le_of_one_le
      · exact one_le_mul_of_one_le_of_one_le hW (one_le_pow₀ (by norm_num))
      · exact Real.one_le_rpow (by norm_num) hA
    · exact one_le_pow₀ (by norm_num)
  have hC : (49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^t)*4^t)*
      (W*(2:ℝ)^(2*i+2*j)) ≤ 784*D := by
    have hp : (2:ℝ)^((i+j)+(2*i+2*j)) ≤ (2:ℝ)^(6*K) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    calc
      _ ≤ (49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*(2:ℝ)^(2*B))*16)*
          (W*(2:ℝ)^(2*i+2*j)) := by gcongr
      _ = 784*W*(2:ℝ)^((i+j)+(2*i+2*j))*(2:ℝ)^A*(2:ℝ)^(2*B) := by rw [pow_add]; ring
      _ ≤ 784*W*(2:ℝ)^(6*K)*(2:ℝ)^A*(2:ℝ)^(2*B) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)) (by positivity)
      _ = _ := by dsimp [D]; ring
  have hmax : max 1 ((49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^t)*4^t)*
      (W*(2:ℝ)^(2*i+2*j))) ≤ 784*D := max_le (by linarith only [hD]) hC
  constructor
  · calc
      _ ≤ (784*D)*16 := mul_le_mul hmax h4 (Real.rpow_nonneg (by norm_num) _) (by linarith only [hD])
      _ ≤ 100000*D := by nlinarith only [hD]
      _ = _ := by dsimp [D]; ring
  · have hexp : t*((B:ℝ)+3)+A ≤ (2*B:ℕ)+6+A := by
      push_cast
      nlinarith only [mul_le_mul_of_nonneg_right ht2 (show 0 ≤ (B:ℝ)+3 by positivity)]
    calc
      _ ≤ 25*(49*((2:ℝ)^i*(2:ℝ)^(((2*B:ℕ):ℝ)+6+A))) := by gcongr; norm_num
      _ = 78400*(2:ℝ)^i*(2:ℝ)^A*(2:ℝ)^(2*B) := by
        rw [Real.rpow_add (by norm_num : (0:ℝ) < 2),
          Real.rpow_add (by norm_num : (0:ℝ) < 2),Real.rpow_natCast]
        norm_num
        ring
      _ ≤ 100000*W*(2:ℝ)^(6*K)*(2:ℝ)^A*(2:ℝ)^(2*B) := by
        have hp : (2:ℝ)^i ≤ (2:ℝ)^(6*K) := pow_le_pow_right₀ (by norm_num) (by omega)
        have hh : (78400:ℝ) ≤ 100000*W := by linarith only [hW]
        gcongr

end Falconer

end OAI
