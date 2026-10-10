import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFParisiContinuity
import OAI.Probability.SKBarriers.Replicas.TripleCDFTrial
import OAI.Probability.SKBarriers.Parisi.SusceptibilityConvergence

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem cdfArea_distance_le {α γ : ℝ → ℝ} (hα : Monotone α) (hγ : Monotone γ)
    {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) :
    |(∫ z in q..1, α z)-(∫ z in q..1,γ z)| ≤ cdfDistance α γ := by
  rw [← intervalIntegral.integral_sub hα.intervalIntegrable hγ.intervalIntegrable]
  have H := cdfDistance_subinterval_le hα hγ (t:=Real.toNNReal (1-q)) hq.1
    (by rw [Real.coe_toNNReal _ (sub_nonneg.mpr hq.2)]; linarith)
  rw [Real.coe_toNNReal _ (sub_nonneg.mpr hq.2),add_sub_cancel] at H
  exact (intervalIntegral.abs_integral_le_integral_abs hq.2).trans H

theorem cdfArea_tendsto {α : ℝ → ℝ} {αn : ℕ → ℝ → ℝ}
    (hα : Monotone α) (hn : ∀ n,Monotone (αn n))
    (hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) :
    Tendsto (fun n => ∫ z in q..1,αn n z) atTop (𝓝 (∫ z in q..1,α z)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using squeeze_zero (fun _ => abs_nonneg _)
    (fun n => cdfArea_distance_le (hn n) hα hq) hD

theorem uniformCDFQuantiles_pointwise_tendsto (α : StieltjesFunction ℝ)
    (hα : ∀ z,α z ∈ Icc (0:ℝ) 1) (hα1 : α 1=1) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    Tendsto (fun n => quantileCDF n (uniformCDFQuantiles n α) s) atTop (𝓝 (α s)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have H := squeeze_zero (fun _ => abs_nonneg _)
    (fun n => quantileCDF_uniformCDFQuantiles_error n α hα hα1 hs)
    (show Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)⁻¹) atTop (𝓝 0) by
      simpa only [Nat.cast_add,Nat.cast_one,one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)))
  simpa only [Real.norm_eq_abs] using H

theorem tripleCDFTrialCoefficient_uniform_tendsto (β : ℝ) (α : StieltjesFunction ℝ)
    (hα : ∀ z,α z ∈ Icc (0:ℝ) 1) (hα1 : α 1=1)
    (K r s₂ : ℝ) {s₁ q : ℝ} (hs : s₁ ∈ Icc (0:ℝ) 1) (hq : q ∈ Icc (0:ℝ) 1) :
    Tendsto (fun n => tripleCDFTrialCoefficient β (quantileCDF n (uniformCDFQuantiles n α)) K r s₁ s₂ q)
      atTop (𝓝 (tripleCDFTrialCoefficient β α K r s₁ s₂ q)) := by
  let αn := fun n => quantileCDF n (uniformCDFQuantiles n α)
  have hn (n z) : αn n z ∈ Icc (0:ℝ) 1 := quantileCDF_bounds n _ z
  have hnm (n) : Monotone (αn n) := quantileCDF_monotone n _
  have hD : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0) := uniformCDFQuantiles_L1_tendsto α hα hα1
  have hχ := scalarCDFSusceptibilityAverage_tendsto β hα α.mono hn hnm hD hq
  have hA := cdfArea_tendsto α.mono hnm hD hq
  have hχ0 := (scalarCDFHessian_tendstoUniformly_interval β hα α.mono hn hnm hD 0 1
    le_rfl le_rfl (by norm_num)).tendsto_at 0
  have hm := uniformCDFQuantiles_pointwise_tendsto α hα hα1 hs
  have hT : Tendsto (fun n => tripleCDFResponse β (αn n) s₂ q) atTop
      (𝓝 (tripleCDFResponse β α s₂ q)) := by
    exact (((hχ.const_mul (β^2)).mul ((hχ0.add_const (2*(β^2*s₂))).add_const (4*(β^2*s₂)^2))).sub_const 1)
  exact (((hχ.sub hA).const_mul (β^2*K)).add
    (((hm.mul hT).add (hT.max tendsto_const_nhds)).const_mul (β^2))).add_const (tripleTimeCommonError β K r)

theorem tripleConstrainedPressure_continuum_trial {N : ℕ} (hN : 0 < N) (β δ : ℝ)
    (α : StieltjesFunction ℝ) (hα : ∀ z,α z ∈ Icc (0:ℝ) 1) (hα1 : α 1=1)
    {r s₁ s₂ q : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s₁) (hs : s₁ < s₂) (hsq : s₂ ≤ q) (hq : q ≤ 1)
    (hD : Nonempty (MatrixStates N 3 (tripleGram r δ q)))
    {a : ℝ} (ha : 0 < a) (hδ : 4*δ^2 ≤ a) (hδ1 : |δ| ≤ 1)
    (hsmall : a*(4*β^2*(s₂-s₁)⁻¹+(2*β^2)^2) ≤ 1/2) :
    matrixConstrainedPressure N 3 β (tripleGram r δ q) ≤
      3*scalarCDFParisi β α+δ^2*tripleCDFTrialCoefficient β α (s₂-s₁)⁻¹ r s₁ s₂ q+
      tripleExpansionConstant a*|δ|^3+β^2*δ^4*((s₂-s₁)⁻¹)^2 := by
  have hC := tripleCDFTrialCoefficient_uniform_tendsto β α hα hα1 (s₂-s₁)⁻¹ r s₂
    (s₁:=s₁) (q:=q) ⟨by linarith,by linarith⟩ ⟨by linarith,hq⟩
  have hP := scalarCDFParisi_tendsto_of_L1 β hα α.mono
    (fun n => quantileCDF_bounds n (uniformCDFQuantiles n α))
    (fun n => quantileCDF_monotone n (uniformCDFQuantiles n α)) (uniformCDFQuantiles_L1_tendsto α hα hα1)
  apply ge_of_tendsto ((((hP.const_mul 3).add (hC.const_mul (δ^2))).add_const
    (tripleExpansionConstant a*|δ|^3)).add_const (β^2*δ^4*((s₂-s₁)⁻¹)^2))
  exact Eventually.of_forall (fun n => tripleConstrainedPressure_quantile_trial hN β δ
    (uniformCDFQuantiles n α) (uniformCDFQuantiles_admissible n α hα1) hr hrs hs hsq hq hD ha hδ hδ1 hsmall)

end SK.Analytic

end
end

end OAI
