import Mathlib
import OAI.Probability.SKSupport.Regularity.TimeStepBound
import OAI.Probability.SKSupport.Diffusion.StepDrift

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

lemma expected_verification_step (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (s h c : ℝ≥0) {Y : Ω → ℝ}
    (hY : Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] Y)
    (hYi : Integrable Y P) {α : ℝ → Ω → ℝ}
    (hαm : Measurable (fun p : ℝ × Ω => α p.1 p.2)) (hαb : ∀ r ω, |α r ω| ≤ 1)
    {F D : ℝ → ℝ → ℝ} (hf : ∀ t, ContDiff ℝ 3 (F t))
    (C₁ C₂ C₃ Ct L : ℝ≥0) (hC₁ : ∀ t x, |deriv (F t) x| ≤ C₁)
    (hC₂ : ∀ t x, |deriv (deriv (F t)) x| ≤ C₂)
    (hC₃ : ∀ t x, |iteratedDeriv 3 (F t) x| ≤ C₃)
    (hDm : Measurable (D s)) (hCt : ∀ x, |D s x| ≤ Ct)
    (hD : ∀ r ∈ Set.Icc (s:ℝ) ((s:ℝ)+(h:ℝ)), ∀ z,
      HasDerivWithinAt (fun t => F t z) (D r z)
        (Set.Icc (s:ℝ) ((s:ℝ)+(h:ℝ))) r)
    (hL : ∀ r ∈ Set.Icc (s:ℝ) ((s:ℝ)+(h:ℝ)), ∀ z x,
      |D r z-D s x| ≤ (L:ℝ)*(|r-(s:ℝ)|+|z-x|))
    (hPDE : ∀ x, D s x + (1/2:ℝ)*deriv (deriv (F s)) x +
      (c:ℝ)/2*(deriv (F s) x)^2 = 0) :
    (∫ ω, F ((s:ℝ)+(h:ℝ)) (Y ω+(B (s+h) ω-B s ω)+stepDrift α s h c ω) ∂P) -
      (∫ ω, F s (Y ω) ∂P) - (∫ ω, stepCost α s h c ω ∂P) ≤
      (C₃:ℝ)/6 * ((h:ℝ)*Real.sqrt (h:ℝ)*normalThirdMoment) +
      (C₂:ℝ)*(c:ℝ)*(h:ℝ) * (Real.sqrt (h:ℝ)*normalFirstMoment + (c:ℝ)*(h:ℝ)) +
      (L:ℝ)*(h:ℝ) * ((h:ℝ) + Real.sqrt (h:ℝ)*normalFirstMoment + (c:ℝ)*(h:ℝ)) := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hYm := hY.mono
    ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le s) le_rfl
  have hAm := stepDrift_measurable hαm s h c h.coe_nonneg
  have hAi := stepDrift_integrable (P := P) hαm hαb s h c h.coe_nonneg c.coe_nonneg
  have hKi := stepCost_integrable (P := P) hαm hαb s h c h.coe_nonneg c.coe_nonneg
  have hG := expected_time_space_step hB hm s h hY hYi hAm c
    (stepDrift_bound hαb s h c h.coe_nonneg c.coe_nonneg) hf
    C₁ C₂ C₃ Ct L hC₁ hC₂ hC₃ hDm hCt hD hL
  have hfd : ContDiff ℝ 2 (deriv (F s)) := (hf s).deriv'
  have hfm : Measurable (fun ω => deriv (F s) (Y ω)) := hfd.continuous.measurable.comp hYm
  have hfi : Integrable (fun ω => deriv (F s) (Y ω)*stepDrift α s h c ω) P :=
    hAi.bdd_mul hfm.aestronglyMeasurable (Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs] using hC₁ s (Y ω)))
  have hdi : Integrable (fun ω => D s (Y ω)) P := Integrable.of_bound
    (hDm.comp hYm).aestronglyMeasurable Ct (Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs] using hCt (Y ω)))
  have hfdd : ContDiff ℝ 1 (deriv (deriv (F s))) := hfd.deriv'
  have hddi : Integrable (fun ω => deriv (deriv (F s)) (Y ω)) P := Integrable.of_bound
    (hfdd.continuous.measurable.comp hYm).aestronglyMeasurable C₂
    (Filter.Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hC₂ s (Y ω)))
  let H (ω : Ω) := deriv (F s) (Y ω)*stepDrift α s h c ω-stepCost α s h c ω +
    (h:ℝ)*(D s (Y ω)+(1/2:ℝ)*deriv (deriv (F s)) (Y ω))
  have hH : (∫ ω, H ω ∂P) ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [] with ω
    have hsq := step_completion_square hαm hαb s h c h.coe_nonneg c.coe_nonneg
      (deriv (F s) (Y ω)) ω
    have he := congrArg (fun z : ℝ => (h:ℝ)*z) (hPDE (Y ω))
    change H ω ≤ 0
    dsimp only [H]
    nlinarith
  have hsub : Integrable (fun ω => deriv (F s) (Y ω)*stepDrift α s h c ω-
      stepCost α s h c ω) P := hfi.sub hKi
  have hadd : Integrable (fun ω => D s (Y ω)+(1/2:ℝ)*deriv (deriv (F s)) (Y ω)) P :=
    hdi.add (hddi.const_mul _)
  dsimp only [H] at hH
  rw [integral_add hsub (hadd.const_mul _), integral_sub hfi hKi,
    integral_const_mul, integral_add hdi (hddi.const_mul _), integral_const_mul] at hH
  have ha := le_abs_self
    ((∫ ω, F ((s:ℝ)+(h:ℝ)) (Y ω+(B (s+h) ω-B s ω)+stepDrift α s h c ω) ∂P) -
      (∫ ω, F s (Y ω) ∂P) -
      (∫ ω, deriv (F s) (Y ω)*stepDrift α s h c ω ∂P) -
      (h:ℝ)*((∫ ω, D s (Y ω) ∂P)+(1/2:ℝ)*(∫ ω, deriv (deriv (F s)) (Y ω) ∂P)))
  linarith

end ZeroTemperatureSK.WeakIto

end
end
end

end OAI
