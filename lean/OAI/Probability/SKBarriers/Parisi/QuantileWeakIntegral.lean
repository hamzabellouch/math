import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFOverlapConvergence
import OAI.Probability.SKBarriers.Parisi.CDFEndpoint
import OAI.Probability.SKBarriers.Parisi.CDFMinimizer
import OAI.Probability.SKBarriers.Parisi.CDFSupportDuality

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem quantileAtomLaw_integrable (k : ℕ) (Q : Fin (k+1) → ℝ) (f : ℝ → ℝ) :
    Integrable f (quantileAtomLaw k Q) := by
  unfold quantileAtomLaw
  apply integrable_finsetSum_measure.mpr
  intro j _
  exact (integrable_dirac (by finiteness)).smul_measure (by finiteness)

theorem quantileAtomLaw_integral (k : ℕ) (Q : Fin (k+1) → ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂quantileAtomLaw k Q)=(1/(k+1:ℕ))*∑ j, f (Q j) := by
  unfold quantileAtomLaw
  rw [integral_finsetSum_measure (fun j _ =>
    (integrable_dirac (by finiteness)).smul_measure (by finiteness))]
  simp only [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal (by positivity :
    0≤((k+1:ℕ):ℝ)⁻¹),smul_eq_mul,← Finset.mul_sum,one_div]

def scalarCDFOverlapTest (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ x, α x∈Icc (0:ℝ) 1) (h1 : α 1=1) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => scalarCDFOverlap β α (projIcc 0 1 (by norm_num) x),
      (continuousOn_iff_continuous_domRestrict.mp
        (scalarCDFOverlap_continuousOn β α ha h1)).comp (continuous_projIcc (h := (by norm_num : (0:ℝ)≤1)))⟩ 1 (by
        intro x y
        rw [Real.dist_eq]
        apply abs_le.mpr
        have hx := scalarCDFOverlap_nonneg_le_one β ha α.mono (projIcc 0 1 (by norm_num) x).property
        have hy := scalarCDFOverlap_nonneg_le_one β ha α.mono (projIcc 0 1 (by norm_num) y).property
        change -1 ≤ scalarCDFOverlap β α (projIcc 0 1 (by norm_num) x)-
          scalarCDFOverlap β α (projIcc 0 1 (by norm_num) y) ∧
          scalarCDFOverlap β α (projIcc 0 1 (by norm_num) x)-
            scalarCDFOverlap β α (projIcc 0 1 (by norm_num) y)≤1
        constructor <;> linarith [hx.1,hx.2,hy.1,hy.2])

theorem scalarCDFOverlapTest_eq (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ x, α x∈Icc (0:ℝ) 1) (h1 : α 1=1) {x : ℝ} (hx : x∈Icc (0:ℝ) 1) :
    scalarCDFOverlapTest β α ha h1 x=scalarCDFOverlap β α x := by
  change scalarCDFOverlap β α (projIcc 0 1 (by norm_num) x)=_
  rw [projIcc_of_mem _ hx]

theorem quantileOverlap_integral_tendsto (β : ℝ) (K : ℕ → ℕ)
    (Q : (n : ℕ) → Fin (K n+1) → ℝ) (hQ : ∀ n, Q n∈admissibleQuantiles (K n))
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (ht : Tendsto (fun n => quantileProbability (K n) (Q n)) atTop (𝓝 μ)) :
    Tendsto (fun n => (1/(K n+1:ℕ))*∑ j, quantileOverlapMean (K n) β (Q n) j)
      atTop (𝓝 (∫ x, scalarCDFOverlap β (cdf (μ : Measure ℝ)) x ∂(μ : Measure ℝ))) := by
  let α := cdf (μ : Measure ℝ)
  have ha (x : ℝ) : α x∈Icc (0:ℝ) 1 := ⟨cdf_nonneg _ _,cdf_le_one _ _⟩
  have h1 : α 1=1 := supported_probability_cdf_one μ hμ
  let f := scalarCDFOverlapTest β α ha h1
  have hf (x : ℝ) (hx : x∈Icc (0:ℝ) 1) : f x=scalarCDFOverlap β α x :=
    scalarCDFOverlapTest_eq β α ha h1 hx
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
      ∫ x, scalarCDFOverlap β α x ∂(μ : Measure ℝ) :=
    integral_congr_ae ((supported_probability_ae μ hμ).mono hf)
  rw [hIμ] at hInt
  let a (n : ℕ) := ∫ x, scalarCDFOverlap β (quantileCDF (K n) (Q n)) x
    ∂quantileAtomLaw (K n) (Q n)
  let b (n : ℕ) := ∫ x, f x ∂quantileAtomLaw (K n) (Q n)
  have hdiff : Tendsto (fun n => a n-b n) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hU) (ε/2) (by positivity)] with n hn
    have H := norm_integral_le_of_norm_le_const (μ:=quantileAtomLaw (K n) (Q n))
      (f:=fun x => scalarCDFOverlap β (quantileCDF (K n) (Q n)) x-f x) (C:=ε/2) (by
        filter_upwards [supported_probability_ae (quantileProbability (K n) (Q n))
          (quantileAtomLaw_supported (K n) (Q n) (hQ n).2)] with x hx
        rw [hf x hx,Real.norm_eq_abs,abs_sub_comm]
        exact (hn x hx).le)
    rw [integral_sub (quantileAtomLaw_integrable _ _ _) (quantileAtomLaw_integrable _ _ _)] at H
    have := quantileAtomLaw_probability (K n) (Q n)
    simp only [Measure.real,measure_univ,ENNReal.toReal_one,mul_one] at H
    rw [Real.dist_eq,sub_zero]
    exact H.trans_lt (by linarith)
  have H := hdiff.add hInt
  simp only [zero_add] at H
  have HE (n : ℕ) : a n-b n+∫ x, f x ∂(quantileProbability (K n) (Q n) : Measure ℝ)=
      (1/(K n+1:ℕ))*∑ j, quantileOverlapMean (K n) β (Q n) j := by
    change a n-b n+b n=_
    rw [sub_add_cancel,show a n=(1/(K n+1:ℕ))*∑ j,
      scalarCDFOverlap β (quantileCDF (K n) (Q n)) (Q n j) from quantileAtomLaw_integral _ _ _]
    simp_rw [scalarCDFOverlap_quantile β (Q n) (hQ n)]
  simpa only [HE] using H

end SK.Analytic

end
end

end OAI
