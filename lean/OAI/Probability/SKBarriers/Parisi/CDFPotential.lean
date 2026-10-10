import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFOptimality
import OAI.Probability.SKBarriers.Parisi.SupportMinima

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def scalarCDFPotential (β : ℝ) (α : ℝ → ℝ) (q : ℝ) : ℝ :=
  ∫ s in q..1, -cdfGradientTest β α s

theorem scalarCDFPotential_eq {β : ℝ} {α : ℝ → ℝ} {q : ℝ}
    (hq : q∈Icc (0:ℝ) 1) :
    scalarCDFPotential β α q=∫ s in q..1, (scalarCDFOverlap β α s-s) := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hq.2] at hs
  dsimp only
  rw [cdfGradientTest_eq ⟨hq.1.trans hs.1,hs.2⟩]
  ring

theorem scalarCDFPotential_hasDerivAt {β : ℝ} {α : ℝ → ℝ}
    (hc : ContinuousOn (scalarCDFOverlap β α) (Icc (0:ℝ) 1)) (q : ℝ) :
    HasDerivAt (scalarCDFPotential β α) (cdfGradientTest β α q) q := by
  have Hc := (cdfGradientTest_continuous hc).neg
  have H := intervalIntegral.integral_hasDerivAt_left
    (Hc.intervalIntegrable q 1) Hc.stronglyMeasurable.stronglyMeasurableAtFilter Hc.continuousAt
  convert H using 1 <;> first | rfl | exact Subsingleton.elim _ _ | simp only [Pi.neg_apply, neg_neg]

theorem scalarCDFPotential_continuous {β : ℝ} {α : ℝ → ℝ}
    (hc : ContinuousOn (scalarCDFOverlap β α) (Icc (0:ℝ) 1)) :
    Continuous (scalarCDFPotential β α) :=
  continuous_iff_continuousAt.mpr (fun q => (scalarCDFPotential_hasDerivAt hc q).continuousAt)

theorem scalarCDFPotential_minimum_bound {β : ℝ} (hβ : β≠0)
    (α : StieltjesFunction ℝ) (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hα1 : α 1=1)
    (hmin : scalarCDFParisi β α=finiteParisiInf β) {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    (∫ s in Icc (0:ℝ) 1, α s*(scalarCDFOverlap β α s-s))≤ scalarCDFPotential β α q := by
  have HG : ContinuousOn (fun s => scalarCDFOverlap β α s-s) (Icc (0:ℝ) 1) :=
    (scalarCDFOverlap_continuousOn β α ha hα1).sub continuousOn_id
  have HI : IntegrableOn (fun s => α s*(scalarCDFOverlap β α s-s)) (Icc (0:ℝ) 1) :=
    (α.mono.monotoneOn _ |>.integrableOn_isCompact isCompact_Icc).mul_continuousOn HG isCompact_Icc
  have H := scalarCDFParisi_minimizer_variation_nonneg hβ α (pointCDF q) ha hα1
    (pointCDF_bounds q) (pointCDF_one hq.2) hmin
  simp_rw [pointCDF_apply,sub_mul] at H
  rw [integral_sub (unitCDF_mul_integrable q HG.integrableOn_Icc) HI,
    unitCDF_mul_integral q hq,← scalarCDFPotential_eq hq] at H
  exact sub_nonneg.mp H

theorem scalarCDFParisi_support_minima {β : ℝ} (hβ : β≠0)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β) :
    ∀ q∈(μ : Measure ℝ).support,
      q∈Icc (0:ℝ) 1 ∧
      scalarCDFPotential β (cdf (μ : Measure ℝ)) q=
        (∫ x, scalarCDFPotential β (cdf (μ : Measure ℝ)) x ∂(μ : Measure ℝ)) ∧
      ∀ r∈Icc (0:ℝ) 1,
        scalarCDFPotential β (cdf (μ : Measure ℝ)) q≤ scalarCDFPotential β (cdf (μ : Measure ℝ)) r := by
  let α := cdf (μ : Measure ℝ)
  have ha : ∀ z, α z∈Icc (0:ℝ) 1 := fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩
  have h1 := supported_probability_cdf_one μ hμ
  have HC := scalarCDFOverlap_continuousOn β α ha h1
  apply support_minima_of_integral_le μ hμ (scalarCDFPotential_continuous HC)
  intro q hq
  have HG : ContinuousOn (fun s => scalarCDFOverlap β α s-s) (Icc (0:ℝ) 1) := HC.sub continuousOn_id
  have HD := supported_cdf_integral_duality μ hμ HG.integrableOn_Icc
  have HE : (∫ x, scalarCDFPotential β α x ∂(μ : Measure ℝ))=
      (∫ x, (∫ s in x..1, scalarCDFOverlap β α s-s) ∂(μ : Measure ℝ)) := by
    apply integral_congr_ae
    filter_upwards [supported_probability_ae μ hμ] with x hx
    exact scalarCDFPotential_eq hx
  rw [HE,← HD]
  exact scalarCDFPotential_minimum_bound hβ α ha h1 hmin hq

theorem scalarCDFParisi_overlap_on_interior_support {β : ℝ} (hβ : β≠0)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β)
    {q : ℝ} (hqs : q∈(μ : Measure ℝ).support) (hq : q∈Ioo (0:ℝ) 1) :
    scalarCDFOverlap β (cdf (μ : Measure ℝ)) q=q := by
  have Hm := (scalarCDFParisi_support_minima hβ μ hμ hmin q hqs).2.2
  have HL : IsLocalMin (scalarCDFPotential β (cdf (μ : Measure ℝ))) q := by
    filter_upwards [Icc_mem_nhds hq.1 hq.2] with r hr
    exact Hm r hr
  have HC := scalarCDFOverlap_continuousOn β (cdf (μ : Measure ℝ))
    (fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩) (supported_probability_cdf_one μ hμ)
  have HE := HL.hasDerivAt_eq_zero (scalarCDFPotential_hasDerivAt HC q)
  rw [cdfGradientTest_eq ⟨hq.1.le,hq.2.le⟩] at HE
  exact (sub_eq_zero.mp HE).symm

end SK.Analytic

end
end

end OAI
