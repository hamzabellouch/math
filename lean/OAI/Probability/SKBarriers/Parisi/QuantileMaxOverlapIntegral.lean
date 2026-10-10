import Mathlib
import OAI.Probability.SKBarriers.Parisi.QuantileWeakIntegral

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem quantileMaxOverlap_integral_tendsto (β : ℝ) (K : ℕ → ℕ)
    (Q : (n : ℕ) → Fin (K n+1) → ℝ) (hQ : ∀ n, Q n∈admissibleQuantiles (K n))
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    {r : ℝ} (hr : r∈Icc (0:ℝ) 1)
    (ht : Tendsto (fun n => quantileProbability (K n) (Q n)) atTop (𝓝 μ)) :
    Tendsto (fun n => (1/(K n+1:ℕ))*∑ j, scalarCDFOverlap β (quantileCDF (K n) (Q n)) (max (Q n j) r))
      atTop (𝓝 (∫ x, scalarCDFOverlap β (cdf (μ : Measure ℝ)) (max x r) ∂(μ : Measure ℝ))) := by
  let α := cdf (μ : Measure ℝ)
  have ha (x : ℝ) : α x∈Icc (0:ℝ) 1 := ⟨cdf_nonneg _ _,cdf_le_one _ _⟩
  have h1 : α 1=1 := supported_probability_cdf_one μ hμ
  let f := (scalarCDFOverlapTest β α ha h1).compContinuous
    ⟨fun x : ℝ => max x r,continuous_id.max continuous_const⟩
  have hf (x : ℝ) (hx : x∈Icc (0:ℝ) 1) : f x=scalarCDFOverlap β α (max x r) :=
    scalarCDFOverlapTest_eq β α ha h1 ⟨hx.1.trans (le_max_left _ _),max_le hx.2 hr.2⟩
  have hcdf (n : ℕ) : cdf (quantileProbability (K n) (Q n) : Measure ℝ)=
      quantileCDF (K n) (Q n) := by
    ext x
    exact cdf_eq_real _ _
  have hD : Tendsto (fun n => cdfDistance (quantileCDF (K n) (Q n)) α) atTop (𝓝 0) := by
    simpa only [cdfDistance,hcdf] using cdf_L1_tendsto_of_weak ht
  have hU := scalarCDFOverlap_tendstoUniformlyOn β ha α.mono
    (fun n => quantileCDF_bounds (K n) (Q n))
    (fun n => quantileCDF_monotone (K n) (Q n)) hD
  have hInt := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp ht f
  have hIμ : (∫ x, f x ∂(μ : Measure ℝ))=
      ∫ x, scalarCDFOverlap β α (max x r) ∂(μ : Measure ℝ) :=
    integral_congr_ae ((supported_probability_ae μ hμ).mono hf)
  rw [hIμ] at hInt
  let a (n : ℕ) := ∫ x, scalarCDFOverlap β (quantileCDF (K n) (Q n)) (max x r)
    ∂quantileAtomLaw (K n) (Q n)
  let b (n : ℕ) := ∫ x, f x ∂quantileAtomLaw (K n) (Q n)
  have hdiff : Tendsto (fun n => a n-b n) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hU) (ε/2) (by positivity)] with n hn
    have H := norm_integral_le_of_norm_le_const (μ:=quantileAtomLaw (K n) (Q n))
      (f:=fun x => scalarCDFOverlap β (quantileCDF (K n) (Q n)) (max x r)-f x) (C:=ε/2) (by
        filter_upwards [supported_probability_ae (quantileProbability (K n) (Q n))
          (quantileAtomLaw_supported (K n) (Q n) (hQ n).2)] with x hx
        rw [hf x hx,Real.norm_eq_abs,abs_sub_comm]
        exact (hn (max x r) ⟨hx.1.trans (le_max_left _ _),max_le hx.2 hr.2⟩).le)
    rw [integral_sub (quantileAtomLaw_integrable _ _ _) (quantileAtomLaw_integrable _ _ _)] at H
    have := quantileAtomLaw_probability (K n) (Q n)
    simp only [Measure.real,measure_univ,ENNReal.toReal_one,mul_one] at H
    rw [Real.dist_eq,sub_zero]
    exact H.trans_lt (by linarith)
  have H := hdiff.add hInt
  simp only [zero_add] at H
  have HE (n : ℕ) : a n-b n+∫ x, f x ∂(quantileProbability (K n) (Q n) : Measure ℝ)=
      (1/(K n+1:ℕ))*∑ j, scalarCDFOverlap β (quantileCDF (K n) (Q n)) (max (Q n j) r) := by
    change a n-b n+b n=_
    rw [sub_add_cancel]
    exact quantileAtomLaw_integral _ _ _
  simpa only [HE] using H

end SK.Analytic

end
end

end OAI
