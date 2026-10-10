import OAI.NumberTheory.TotientAsymptotic.BootstrapRealCount
import OAI.NumberTheory.TotientAsymptotic.DyadicLogGeometry

namespace OAI

/-! The dyadic counting envelope and its normality factor at real endpoints. -/
noncomputable section
namespace TotientAsymptotic

theorem counting_envelope_real_bound : ∃ C : ℝ,0 < C ∧ ∀ x : ℝ,4 ≤ x →
    dyadicTotientEnvelope (countingDyadicIndex x) ≤
      C*Real.exp (9*(Real.log (B x+4))^2) := by
  obtain ⟨C,hC,hcount⟩ := bootstrap_envelope_bound
  refine ⟨C,hC,?_⟩
  intro x hx
  have hheight := (counting_dyadic_index_bounds hx).2.2
  have hH := bootstrapHeight_one_le (countingDyadicIndex x)
  have hlo : 0 ≤ Real.log (bootstrapHeight (countingDyadicIndex x)) := Real.log_nonneg hH
  have hle := Real.log_le_log (by linarith) hheight
  apply (hcount _).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  change 9*(Real.log (bootstrapHeight (countingDyadicIndex x)))^2 ≤ _
  nlinarith

lemma counting_normality_polynomial {x : ℝ} (hx : 4 ≤ x) (hB : 0 ≤ B x) :
    (B (2*x))^5*(1+Real.log (countingDyadicIndex x)) ≤ (B x+4)^6 := by
  have hbounds := counting_dyadic_index_bounds hx
  have hBupper := double_log_double_le (show 2 ≤ x by linarith)
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hBmono : B x ≤ B (2*x) := by
    apply Real.log_le_log hlogx
    exact Real.log_le_log hx0 (by linarith)
  have hlog : 1+Real.log (countingDyadicIndex x) ≤ B x+4 := by
    have hJ0 : (0:ℝ) < countingDyadicIndex x := by
      exact_mod_cast (show 0 < countingDyadicIndex x by omega)
    have hh := Real.log_le_log hJ0 (show (countingDyadicIndex x:ℝ) ≤ (countingDyadicIndex x:ℝ)+1 by linarith)
    have hheight := hbounds.2.2
    change 1+Real.log ((countingDyadicIndex x:ℝ)+1) ≤ B x+4 at hheight
    linarith
  have hlog0 : 0 ≤ 1+Real.log (countingDyadicIndex x) := by
    have hh := Real.log_nonneg (show (1:ℝ) ≤ countingDyadicIndex x by exact_mod_cast hbounds.1)
    linarith
  calc
    _ ≤ (B x+4)^5*(B x+4) := mul_le_mul
      (pow_le_pow_left₀ (hB.trans hBmono) (by linarith) 5) hlog hlog0 (by positivity)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
