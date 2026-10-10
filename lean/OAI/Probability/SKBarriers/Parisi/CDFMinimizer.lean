import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarLimitCandidate
import OAI.Probability.SKBarriers.SpinGlass.FiniteLaw
import OAI.Probability.SKBarriers.Parisi.CDFUniformQuantiles
import OAI.Probability.SKBarriers.Parisi.CDFParisiContinuity

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem finiteParisiInf_le_scalarCDFParisi (β : ℝ) (α : StieltjesFunction ℝ)
    (hα : ∀ z, α z ∈ Icc (0:ℝ) 1) (hα1 : α 1=1) :
    finiteParisiInf β ≤ scalarCDFParisi β α := by
  have ht := scalarCDFParisi_tendsto_of_L1 β hα α.mono
    (fun k => quantileCDF_bounds k (uniformCDFQuantiles k α))
    (fun k => quantileCDF_monotone k (uniformCDFQuantiles k α))
    (uniformCDFQuantiles_L1_tendsto α hα hα1)
  apply ge_of_tendsto ht
  apply Eventually.of_forall
  intro k
  rw [scalarCDFParisi_quantile β _ (uniformCDFQuantiles_admissible k α hα1)]
  exact finiteParisiInf_le β _ (uniformCDFQuantiles_admissible k α hα1).1
    (uniformCDFQuantiles_admissible k α hα1).2

theorem supported_probability_cdf_one (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1) : cdf (μ : Measure ℝ) 1=1 := by
  have H : (μ : Measure ℝ) (Iic 1)=1 := le_antisymm prob_le_one
    (by rw [← hμ]; exact measure_mono Icc_subset_Iic_self)
  rw [cdf_eq_real,Measure.real,H,ENNReal.toReal_one]

theorem exists_scalarCDFParisi_minimizer (β : ℝ) :
    ∃ μ : ProbabilityMeasure ℝ, (μ : Measure ℝ) (Icc (0:ℝ) 1)=1 ∧
      scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β ∧
      ∀ ν : ProbabilityMeasure ℝ, (ν : Measure ℝ) (Icc (0:ℝ) 1)=1 →
        scalarCDFParisi β (cdf (μ : Measure ℝ)) ≤ scalarCDFParisi β (cdf (ν : Measure ℝ)) := by
  obtain ⟨μ,K,A,hμ,hA,_,_,hv,hL⟩ := exists_stationary_quantile_L1_limit β
  have ht := scalarCDFParisi_tendsto_of_L1 β
    (fun z => ⟨cdf_nonneg (μ : Measure ℝ) z,cdf_le_one (μ : Measure ℝ) z⟩)
    (cdf (μ : Measure ℝ)).mono
    (fun n => quantileCDF_bounds (K n) (A n))
    (fun n => quantileCDF_monotone (K n) (A n)) hL
  have he (n : ℕ) : scalarCDFParisi β (quantileCDF (K n) (A n))=
      extendedQuantileParisi (K n) β (A n) := scalarCDFParisi_quantile β (A n) (hA n)
  simp_rw [he] at ht
  have H := tendsto_nhds_unique ht hv
  refine ⟨μ,hμ,H,fun ν hν => ?_⟩
  rw [H]
  exact finiteParisiInf_le_scalarCDFParisi β (cdf (ν : Measure ℝ))
    (fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩) (supported_probability_cdf_one ν hν)

end SK.Analytic

end
end

end OAI
