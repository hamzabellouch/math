import OAI.MeasureTheory.Falconer.Incidence.ProfileBlockBudget
import OAI.MeasureTheory.Falconer.Recursion.UniformScaleBudgets

namespace OAI

/-! One explicit budget for the two branches of the endpoint scale product. -/
namespace Falconer

noncomputable def profileStepBudget (H G W : ℝ) : ℝ := 1024*W^2*H^3*G

theorem profile_retention_cost_le {W H : ℝ} (hW : 0 ≤ W) (hH : 0 ≤ H)
    {i j K : ℕ} (hi : i ≤ K) (hj : j ≤ K) (B : ℕ) :
    (W*(2:ℝ)^(2*i))*((H*(2:ℝ)^j)*((2*B+1:ℕ):ℝ)^K) ≤
      W*H*((2:ℝ)^(3*K)*((2*B+1:ℕ):ℝ)^K) := by
  calc
    _ = W*H*((2:ℝ)^(2*i+j)*((2*B+1:ℕ):ℝ)^K) := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) (by omega : 2*i+j ≤ 3*K)) (by positivity))
      (mul_nonneg hW hH)

theorem profile_step_budget_bounds {H G W : ℝ} (hH : 1 ≤ H) (hG : 1 ≤ G) (hW : 1 ≤ W) :
    W ≤ profileStepBudget H G W ∧ 4*H ≤ profileStepBudget H G W ∧
      280*W*H^3 ≤ profileStepBudget H G W ∧
      672*W^2*H^3 ≤ profileStepBudget H G W ∧
      32*W*H^3 ≤ profileStepBudget H G W ∧
      W*(20*H^2)*G ≤ profileStepBudget H G W ∧
      W*(16*W*H^3)*G ≤ profileStepBudget H G W := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hG0 : 0 ≤ G := zero_le_one.trans hG
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hW2 : W ≤ W^2 := by nlinarith only [hW]
  have hH2 : H^2 ≤ H^3 := by nlinarith only [sq_nonneg H,mul_le_mul_of_nonneg_left hH (sq_nonneg H)]
  have hH3 : 1 ≤ H^3 := one_le_pow₀ hH
  have hW21 : 1 ≤ W^2 := one_le_pow₀ hW
  have hHH3 : H ≤ H^3 := (show H ≤ H^2 by nlinarith only [hH]).trans hH2
  have hcore : W^2*H^3 ≤ profileStepBudget H G W := by
    dsimp [profileStepBudget]
    calc
      _ ≤ 1024*(W^2*H^3) := by nlinarith only [mul_nonneg (sq_nonneg W) (pow_nonneg hH0 3)]
      _ ≤ _ := by
        convert le_mul_of_one_le_right (show 0 ≤ 1024*(W^2*H^3) by positivity) hG using 1; ring
  have bound {c : ℝ} (_hc : 0 ≤ c) (hc' : c ≤ 1024) :
      c*W^2*H^3*G ≤ profileStepBudget H G W := by
    dsimp [profileStepBudget]
    gcongr
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · exact (hW2.trans (le_mul_of_one_le_right (sq_nonneg W) hH3)).trans hcore
  · calc
      4*H ≤ 4*W^2*H^3*G := by
        calc
          _ ≤ 4*W^2*H^3 := by
            calc
              _ ≤ 4*H^3 := mul_le_mul_of_nonneg_left hHH3 (by norm_num)
              _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hW21 (pow_nonneg hH0 3)]
          _ ≤ _ := le_mul_of_one_le_right (by positivity) hG
      _ ≤ _ := bound (by norm_num) (by norm_num)
  · calc
      _ ≤ 280*W^2*H^3 := by gcongr
      _ ≤ 280*W^2*H^3*G := le_mul_of_one_le_right (by positivity) hG
      _ ≤ _ := bound (by norm_num) (by norm_num)
  · exact (le_mul_of_one_le_right (by positivity) hG).trans
      (bound (c := 672) (by norm_num) (by norm_num))
  · calc
      _ ≤ 32*W^2*H^3 := by gcongr
      _ ≤ 32*W^2*H^3*G := le_mul_of_one_le_right (by positivity) hG
      _ ≤ _ := bound (by norm_num) (by norm_num)
  · calc
      _ = 20*W*H^2*G := by ring
      _ ≤ 20*W^2*H^3*G := by gcongr
      _ ≤ _ := bound (by norm_num) (by norm_num)
  · calc
      _ = 16*W^2*H^3*G := by ring
      _ ≤ _ := bound (by norm_num) (by norm_num)

theorem profile_label_cost_one_le (B K : ℕ) :
    1 ≤ (2:ℝ)^(3*K)*((2*B+1:ℕ):ℝ)^K := by
  apply one_le_mul_of_one_le_of_one_le
  · exact one_le_pow₀ (by norm_num)
  · apply one_le_pow₀
    exact_mod_cast (show 1 ≤ 2*B+1 by omega)

end Falconer

end OAI
