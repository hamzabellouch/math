import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFSupportContact
import OAI.Probability.SKBarriers.Parisi.CDFHeatContact

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem cdf_zero_below_least_support (μ : ProbabilityMeasure ℝ) {q z : ℝ}
    (hq : IsLeast (μ : Measure ℝ).support q) (hz : z<q) :
    cdf (μ : Measure ℝ) z=0 := by
  have H : (μ : Measure ℝ) (Iic z)=0 := by
    apply measure_mono_null (t:=(μ : Measure ℝ).supportᶜ) _ (μ : Measure ℝ).measure_compl_support
    intro x hx hs
    exact (not_le_of_gt hz) (le_trans (hq.2 hs) hx)
  rw [cdf_eq_real,measureReal_def,H,ENNReal.toReal_zero]

theorem scalarCDFParisi_zero_mem_support {β : ℝ} (hβ : β≠0)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β) :
    (0:ℝ)∈(μ : Measure ℝ).support := by
  have HS := Measure.support_subset_of_isClosed (μ:=(μ : Measure ℝ))
    isClosed_Icc (supported_probability_ae μ hμ)
  have HC : IsCompact (μ : Measure ℝ).support :=
    isCompact_Icc.of_isClosed_subset (μ : Measure ℝ).isClosed_support HS
  obtain ⟨q,hq⟩ := HC.exists_isLeast ((μ : Measure ℝ).nonempty_support (by
    intro H
    have H1 := measure_univ (μ:=(μ : Measure ℝ))
    simp only [H,Measure.coe_zero,Pi.zero_apply,zero_ne_one] at H1))
  have hbound := HS hq.1
  have he : q=0 := by
    by_contra H
    have hq0 : 0<q := lt_of_le_of_ne hbound.1 (Ne.symm H)
    have hm := (scalarCDFParisi_support_minima hβ μ hμ hmin q hq.1).2.2
    exact scalarCDFPotential_not_min_heat_prefix β (cdf (μ : Measure ℝ))
      (fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩) (supported_probability_cdf_one μ hμ)
      hq0 hbound.2 (fun z hz => cdf_zero_below_least_support μ hq hz.2)
      (scalarCDFParisi_overlap_on_support hβ μ hμ hmin hq.1) hm
  simpa only [he] using hq.1

theorem cdf_pos_of_zero_mem_support (μ : ProbabilityMeasure ℝ)
    (h0 : (0:ℝ)∈(μ : Measure ℝ).support) {s : ℝ} (hs : 0<s) :
    0<cdf (μ : Measure ℝ) s := by
  have H : 0<(μ : Measure ℝ) (Iic s) :=
    (Measure.mem_support_iff_forall (μ:=(μ : Measure ℝ)) 0).mp h0 _ (Iic_mem_nhds hs)
  rw [cdf_eq_real,measureReal_def]
  exact ENNReal.toReal_pos H.ne' (measure_ne_top _ _)

theorem cdf_area_strict (μ : ProbabilityMeasure ℝ)
    (h0 : (0:ℝ)∈(μ : Measure ℝ).support) {h : ℝ} (hh : 0<h) :
    (∫ s in h..1, cdf (μ : Measure ℝ) s)<(∫ s in (0:ℝ)..1, cdf (μ : Measure ℝ) s) := by
  have HI (a b : ℝ) : IntervalIntegrable (cdf (μ : Measure ℝ)) volume a b :=
    (cdf (μ : Measure ℝ)).mono.intervalIntegrable
  have HP := intervalIntegral.intervalIntegral_pos_of_pos_on (HI 0 h)
    (fun s hs => cdf_pos_of_zero_mem_support μ h0 hs.1) hh
  have HE := intervalIntegral.integral_add_adjacent_intervals (HI 0 h) (HI h 1)
  linarith

end SK.Analytic

end
end

end OAI
