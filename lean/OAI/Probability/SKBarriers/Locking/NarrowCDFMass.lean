import Mathlib

namespace OAI

section

noncomputable section
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem cdf_sub_le_real_Icc (μ : ProbabilityMeasure ℝ) {a b : ℝ} (hab : a≤b) :
    cdf (μ : Measure ℝ) b-cdf (μ : Measure ℝ) a≤(μ : Measure ℝ).real (Icc a b) := by
  have H := (cdf (μ : Measure ℝ)).measure_Ioc a b
  rw [measure_cdf] at H
  have He : (μ : Measure ℝ).real (Ioc a b)=cdf (μ : Measure ℝ) b-cdf (μ : Measure ℝ) a := by
    rw [measureReal_def,H,ENNReal.toReal_ofReal (sub_nonneg.mpr ((cdf (μ : Measure ℝ)).mono hab))]
  rw [← He]
  exact measureReal_mono Ioc_subset_Icc_self

end SK.Analytic

end
end

end OAI
