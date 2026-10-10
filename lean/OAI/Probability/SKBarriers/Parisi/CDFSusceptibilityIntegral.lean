import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFDerivativeConvergence
import OAI.Probability.SKBarriers.Hierarchy.HierarchyAtomCoordinates
import OAI.Probability.SKBarriers.Parisi.QuantileWeakIntegral
import OAI.Probability.SKBarriers.Parisi.QuantileSpatial

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFHessian_weak_quantile_limit (β : ℝ) (K : ℕ → ℕ)
    (Q : (n : ℕ) → Fin (K n+1) → ℝ) (hQ : ∀ n, Q n∈admissibleQuantiles (K n))
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (ht : Tendsto (fun n => quantileProbability (K n) (Q n)) atTop (𝓝 μ)) :
    scalarCDFHessian β (cdf (μ : Measure ℝ)) 0 1 0=
      1-∫ x, scalarCDFOverlap β (cdf (μ : Measure ℝ)) x ∂(μ : Measure ℝ) := by
  have hcdf (n : ℕ) : cdf (quantileProbability (K n) (Q n) : Measure ℝ)=
      quantileCDF (K n) (Q n) := by ext x; exact cdf_eq_real _ _
  have hD : Tendsto (fun n => cdfDistance (quantileCDF (K n) (Q n))
      (cdf (μ : Measure ℝ))) atTop (𝓝 0) := by
    simpa only [cdfDistance,hcdf] using cdf_L1_tendsto_of_weak ht
  have HU := scalarCDFHessian_tendstoUniformly β
    (fun x => ⟨cdf_nonneg (μ : Measure ℝ) x,cdf_le_one (μ : Measure ℝ) x⟩)
    (cdf (μ : Measure ℝ)).mono (fun n => quantileCDF_bounds (K n) (Q n))
    (fun n => quantileCDF_monotone (K n) (Q n)) hD
  have HE (n : ℕ) : scalarCDFHessian β (quantileCDF (K n) (Q n)) 0 1 0=
      1-(1/(K n+1:ℕ))*∑ j, quantileOverlapMean (K n) β (Q n) j := by
    rw [scalarCDFHessian_quantile β (Q n) (hQ n)]
    exact finiteScalar_hessian_quantile (K n) β (Q n)
  have HT := HU.tendsto_at 0
  simp_rw [HE] at HT
  exact tendsto_nhds_unique HT
    ((quantileOverlap_integral_tendsto β K Q hQ μ hμ ht).const_sub 1)

theorem exists_scalarCDFParisi_minimizer_susceptibility (β : ℝ) :
    ∃ μ : ProbabilityMeasure ℝ, (μ : Measure ℝ) (Icc (0:ℝ) 1)=1 ∧
      scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β ∧
      scalarCDFHessian β (cdf (μ : Measure ℝ)) 0 1 0=
        1-∫ x, scalarCDFOverlap β (cdf (μ : Measure ℝ)) x ∂(μ : Measure ℝ) := by
  obtain ⟨K,Q,hQ,_,_,hv⟩ := exists_stationary_quantile_sequence β
  obtain ⟨μ,hμ,φ,hφ,ht⟩ := quantileProbability_weak_subsequence K Q (fun n => (hQ n).2)
  have hcdf (n : ℕ) : cdf (quantileProbability (K (φ n)) (Q (φ n)) : Measure ℝ)=
      quantileCDF (K (φ n)) (Q (φ n)) := by ext x; exact cdf_eq_real _ _
  have hD : Tendsto (fun n => cdfDistance (quantileCDF (K (φ n)) (Q (φ n)))
      (cdf (μ : Measure ℝ))) atTop (𝓝 0) := by
    simpa only [cdfDistance,hcdf] using cdf_L1_tendsto_of_weak ht
  have HP := scalarCDFParisi_tendsto_of_L1 β
    (fun x => ⟨cdf_nonneg (μ : Measure ℝ) x,cdf_le_one (μ : Measure ℝ) x⟩)
    (cdf (μ : Measure ℝ)).mono
    (fun n => quantileCDF_bounds (K (φ n)) (Q (φ n)))
    (fun n => quantileCDF_monotone (K (φ n)) (Q (φ n))) hD
  simp_rw [scalarCDFParisi_quantile β _ (hQ _)] at HP
  exact ⟨μ,hμ,tendsto_nhds_unique HP (hv.comp hφ.tendsto_atTop),
    scalarCDFHessian_weak_quantile_limit β (fun n => K (φ n)) (fun n => Q (φ n))
      (fun n => hQ (φ n)) μ hμ ht⟩

end SK.Analytic

end
end

end OAI
