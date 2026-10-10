import OAI.MeasureTheory.Falconer.Estimates.ScalarCoefficientLogBudget

namespace OAI

/-! The normalization cost grows at most polynomially with the weak
 Frostman constant and the original projection bound. -/
namespace Falconer

def scalarNormalizedBaseConstant : ℝ := 5762+2*scalarCoefficientBudget 1 1 3

 theorem scalar_normalized_base_bound (M : ℕ) {K : ℝ} (hK : 1 ≤ K) :
    scalarNormalizedBaseBudget M K ≤ scalarNormalizedBaseConstant*((M:ℝ)+8)*K^512 := by
  have hH : 0 ≤ scalarCoefficientBudget 1 1 3 :=
    (by norm_num : (0:ℝ) ≤ 1).trans (scalarCoefficientBudget_one_le 1 (by norm_num) 3)
  have hK0 : 0 ≤ K := by linarith
  have hp1 : 1 ≤ K^512 := one_le_pow₀ hK
  have hp2 : K ≤ K^512 := by
    simpa only [pow_one] using pow_le_pow_right₀ hK (show 1 ≤ (512:ℕ) by omega)
  have hp7 : K^7 ≤ K^512 := pow_le_pow_right₀ hK (by omega)
  have hfactor : scalarCoefficientBudget 1 K 3 = scalarCoefficientBudget 1 1 3*K^512 := by
    simpa using scalarCoefficientBudget_factor 1 K 3
  have hh : scalarNormalizedBaseBudget M K ≤
      (5762+(2*(M:ℝ)+3)*scalarCoefficientBudget 1 1 3)*K^512 := by
    unfold scalarNormalizedBaseBudget
    rw [hfactor,mul_pow]
    norm_num only [show (2:ℝ)^7 = 128 by norm_num]
    nlinarith
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hK0 _)
  unfold scalarNormalizedBaseConstant
  nlinarith [(Nat.cast_nonneg M : (0:ℝ) ≤ (M:ℝ))]

 theorem scalar_normalized_base_one_le (M : ℕ) {K : ℝ} (hK : 1 ≤ K) :
    1 ≤ scalarNormalizedBaseBudget M K := by
  have hK0 : 0 ≤ K := by linarith
  have hH : 0 ≤ scalarCoefficientBudget 1 K 3 :=
    (by norm_num : (0:ℝ) ≤ 1).trans (scalarCoefficientBudget_one_le 1 hK 3)
  have hp : 0 ≤ 45*(2*K)^7 := by positivity
  have hm : 0 ≤ (2*(M:ℝ)+3)*scalarCoefficientBudget 1 K 3 := by positivity
  unfold scalarNormalizedBaseBudget
  linarith

 theorem scalar_normalized_log_budget :
    ∃ c p q : ℝ, 0 ≤ c ∧ 0 ≤ p ∧ 0 ≤ q ∧ ∀ M : ℕ, ∀ K : ℝ, 1 ≤ K →
      Real.log (scalarNormalizedProjectionBudget M K) ≤
        c+p*Real.log ((M:ℝ)+10)+q*Real.log K := by
  obtain ⟨c,p,hc,hp,hbudget⟩ := scalar_coefficient_log_budget 5
  have hC : 1 ≤ scalarNormalizedBaseConstant := by
    have hh := scalarCoefficientBudget_one_le 1 (K := (1:ℝ)) (by norm_num) 3
    unfold scalarNormalizedBaseConstant
    linarith
  have hClog : 0 ≤ Real.log scalarNormalizedBaseConstant := Real.log_nonneg hC
  refine ⟨c+32768*Real.log scalarNormalizedBaseConstant,p+32768,16777216,
    by positivity,by positivity,by norm_num,?_⟩
  intro M K hK
  have hb := hbudget (M+2) (scalarNormalizedBaseBudget M K)
    (scalar_normalized_base_one_le M hK)
  have hl := Real.log_le_log (lt_of_lt_of_le (by norm_num) (scalar_normalized_base_one_le M hK))
    (scalar_normalized_base_bound M hK)
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_pow] at hl
  have hm := Real.log_le_log (by positivity : (0:ℝ) < (M:ℝ)+8)
    (show (M:ℝ)+8 ≤ (M:ℝ)+10 by linarith)
  have hpm := mul_le_mul_of_nonneg_left hm (show (0:ℝ) ≤ 32768 by norm_num)
  change Real.log (scalarCoefficientBudget (M+2) (scalarNormalizedBaseBudget M K) 5) ≤ _
  push_cast at hb
  rw [show (M:ℝ)+2+8 = (M:ℝ)+10 by ring] at hb
  norm_num only [Nat.cast_ofNat,show (8:ℝ)^5 = 32768 by norm_num] at hb hl
  nlinarith

end Falconer

end OAI
