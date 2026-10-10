import OAI.NumberTheory.JointDickman.Analysis.LogRieszDerivatives
import OAI.NumberTheory.JointDickman.Amplification.LogScaleComparison

namespace OAI

/-! # Uniform bounds for logarithmic Riesz monomials and second derivatives -/
namespace JointDickman

theorem log_rpow_near_scale_below {β γ x t : ℝ} (hβ : β ≤ γ)
    (hx : 0 < x) (hlog : 2 ≤ Real.log x) (ht : t ∈ Set.Icc (x/2) (2*x)) :
    (Real.log t)^β ≤ (2:ℝ)^(|β|)*(Real.log x)^γ := by
  exact (log_rpow_near_scale β hx hlog ht).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith) hβ)
      (Real.rpow_nonneg (by norm_num) _))

theorem logRieszMonomial_bound (β : ℝ) {x t : ℝ} (hx : 0 < x)
    (hlog : 2 ≤ Real.log x) (ht : t ∈ Set.Icc (x/2) (2*x)) :
    |logRieszMonomial β t| ≤ (4*(2:ℝ)^(|β|))*x^2*(Real.log x)^β := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity : 0 < x/2) ht.1
  have hlogt : 0 < Real.log t := by have := (log_near_scale hx hlog ht).1; linarith
  have hpow : t^2 ≤ 4*x^2 := by nlinarith [ht.2]
  rw [logRieszMonomial,abs_of_nonneg (by positivity)]
  calc
    _ ≤ (4*x^2)*((2:ℝ)^(|β|)*(Real.log x)^β) :=
      mul_le_mul hpow (log_rpow_near_scale β hx hlog ht)
        (Real.rpow_nonneg hlogt.le _) (by positivity)
    _ = _ := by ring

theorem logRieszSecondDerivative_bound (β : ℝ) {x t : ℝ} (hx : 0 < x)
    (hlog : 2 ≤ Real.log x) (ht : t ∈ Set.Icc (x/2) (2*x)) :
    |logRieszSecondDerivative β t| ≤
      (2*(2:ℝ)^(|β|)+3*|β| *(2:ℝ)^(|β-1|)+|β*(β-1)| *(2:ℝ)^(|β-2|))*(Real.log x)^β := by
  have hlogt : 0 < Real.log t := by have := (log_near_scale hx hlog ht).1; linarith
  have h0 := log_rpow_near_scale_below (le_refl β) hx hlog ht
  have h1 := log_rpow_near_scale_below (show β-1 ≤ β by linarith) hx hlog ht
  have h2 := log_rpow_near_scale_below (show β-2 ≤ β by linarith) hx hlog ht
  calc
    _ ≤ 2*(Real.log t)^β+3*|β| *(Real.log t)^(β-1)+|β*(β-1)| *(Real.log t)^(β-2) := by
      unfold logRieszSecondDerivative
      calc
        _ ≤ |2*(Real.log t)^β+3*β*(Real.log t)^(β-1)|+
            |β*(β-1)*(Real.log t)^(β-2)| := abs_add_le _ _
        _ ≤ |2*(Real.log t)^β|+|3*β*(Real.log t)^(β-1)|+
            |β*(β-1)*(Real.log t)^(β-2)| := by
          linarith [abs_add_le (2*(Real.log t)^β) (3*β*(Real.log t)^(β-1))]
        _ = _ := by
          simp only [abs_mul,abs_of_nonneg (Real.rpow_nonneg hlogt.le _)]
          norm_num
    _ ≤ 2*((2:ℝ)^(|β|)*(Real.log x)^β)+
        3*|β| *((2:ℝ)^(|β-1|)*(Real.log x)^β)+
        |β*(β-1)| *((2:ℝ)^(|β-2|)*(Real.log x)^β) := by gcongr
    _ = _ := by ring

end JointDickman

end OAI
