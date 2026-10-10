import OAI.MeasureTheory.Falconer.Estimates.ScalarParameterChoice

namespace OAI

/-! The fixed block parameters absorb the initial regularization loss
 both in the final projection cardinality and in prefix nonconcentration. -/
namespace Falconer

 theorem scalar_regularization_loss {B P M : ℕ} {κ : ℝ} (hM : 0 < M) (hκ : 0 ≤ κ)
    (hR : Real.log (2050*(B+1)^2:ℝ) ≤ κ*(P:ℝ)*Real.log 2/200) :
    Real.log (((2050*(B+1)^2:ℝ)^(M+1))) ≤ κ*(P:ℝ)*(M:ℝ)*Real.log 2/100 := by
  rw [Real.log_pow]
  have hm : (M:ℝ)+1 ≤ 2*(M:ℝ) := by exact_mod_cast (show M+1 ≤ 2*M by omega)
  have ha : 0 ≤ κ*(P:ℝ)*Real.log 2/200 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg (M+1))
  have h2 := mul_le_mul_of_nonneg_right hm ha
  push_cast at h1 ⊢
  nlinarith

 theorem scalar_regularization_scale_budget {B P M : ℕ} {κ K : ℝ}
    (hM : 0 < M) (hκ : 0 < κ) (hK : 0 < K)
    (hB : 800*(P:ℝ) ≤ κ*(B:ℝ))
    (hR : Real.log (2050*(B+1)^2:ℝ) ≤ κ*(P:ℝ)*Real.log 2/200)
    (hscale : 40*Real.log K ≤ (κ*(B:ℝ)-2*(P:ℝ))*κ*(M:ℝ)*Real.log 2) :
    20*Real.log (K*(2050*(B+1)^2:ℝ)^(M+1)) ≤
      (κ*(B:ℝ)-2*(P:ℝ))*κ*(M:ℝ)*Real.log 2 := by
  have hloss := scalar_regularization_loss hM hκ.le hR
  have hc : (P:ℝ)/5 ≤ (κ*(B:ℝ)-2*(P:ℝ))/2 := by
    have hp : 0 ≤ (P:ℝ) := Nat.cast_nonneg _
    linarith
  have hh := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ κ*(M:ℝ)*Real.log 2 by positivity)
  rw [Real.log_mul hK.ne' (by positivity)]
  nlinarith

 theorem scalar_regularization_gain {B P M : ℕ} {κ : ℝ} (hM : 0 < M) (hκ : 0 ≤ κ)
    (hR : Real.log (2050*(B+1)^2:ℝ) ≤ κ*(P:ℝ)*Real.log 2/200) :
    Real.exp ((κ/25)*(P:ℝ)*(M:ℝ)*Real.log 2)*(2050*(B+1)^2:ℝ)^(M+1) ≤
      Real.exp ((κ/20)*(P:ℝ)*(M:ℝ)*Real.log 2) := by
  have hloss := scalar_regularization_loss hM hκ hR
  have hp : 0 < (2050*(B+1)^2:ℝ)^(M+1) := by positivity
  rw [← Real.exp_log hp,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

end Falconer

end OAI
