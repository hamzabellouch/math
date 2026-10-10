import Mathlib
import OAI.Probability.LogConcave.Sampling.Jet

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r) (hlam : 0<lam)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0<T) (hT1 : T<1)

include hlam in
lemma terminalActionChain_quotient {t : ℝ} (ht : t∈Ioc (0:ℝ) T) (p : Point d × Point d) :
    t⁻¹ • terminalActionChain hF x hr hl hT0 hT1 1 (t,p)=
      r • (steinIntegrand hF x hr hl hT0.le hT1 (t,p.1)) p.2 := by
  have he := terminalJacobian_action_quotient hF x hr hlam hl hT0 hT1 ⟨t,ht⟩ p.1 p.2
  rw [←(terminalActionChain_hasDerivAt hF x hr hl hT0 hT1 0 t p).deriv]
  exact he

include hlam in

theorem terminalActionChain_integral (p : Point d × Point d) :
    (∫t in (0:ℝ)..T,t⁻¹ • terminalActionChain hF x hr hl hT0 hT1 1 (t,p))=
      r • (centeringKernel hF x hr hl hT0.le hT1 p.1).adjoint p.2 := by
  have hc : Continuous (fun t => steinIntegrand hF x hr hl hT0.le hT1 (t,p.1)) :=
    (steinIntegrand_smooth hF x hr hlam hl hT0.le hT1).continuous.comp
      (continuous_id.prodMk continuous_const)
  calc
    _ = ∫t in (0:ℝ)..T,r • (steinIntegrand hF x hr hl hT0.le hT1 (t,p.1)) p.2 := by
      apply intervalIntegral.integral_congr_ae'
      · exact Filter.Eventually.of_forall (fun _ ht => terminalActionChain_quotient hF x hr hlam hl hT0 hT1 ht p)
      · exact Filter.Eventually.of_forall (fun _ ht => False.elim (not_lt_of_ge (le_trans ht.2 hT0.le) ht.1))
    _ = r • (∫t in (0:ℝ)..T,steinIntegrand hF x hr hl hT0.le hT1 (t,p.1)) p.2 := by
      rw [intervalIntegral.integral_smul,ContinuousLinearMap.intervalIntegral_apply (hc.intervalIntegrable _ _)]
    _ = _ := by
      rw [centeringKernel,ContinuousLinearMap.adjoint_adjoint,integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le hT0.le]
end LogConcaveSampling

end

end

end OAI
