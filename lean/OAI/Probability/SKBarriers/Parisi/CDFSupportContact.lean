import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFEndpoint
import OAI.Probability.SKBarriers.Parisi.CDFPotential

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem derivative_nonpos_at_right_minimum {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 1) (hm : ∀ r∈Icc (0:ℝ) 1, f 1≤f r) : d≤0 := by
  have H := (hasDerivAt_iff_tendsto_slope_left_right.mp hd).1
  apply le_of_tendsto H
  have HP : ∀ᶠ r : ℝ in 𝓝[<] (1:ℝ), 0<r :=
    (eventually_gt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [HP,self_mem_nhdsWithin] with r hr0 hr1
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hm r ⟨hr0.le,hr1.le⟩))
    (sub_nonpos.mpr hr1.le)

theorem scalarCDFParisi_overlap_on_support {β : ℝ} (hβ : β≠0)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β)
    {q : ℝ} (hqs : q∈(μ : Measure ℝ).support) :
    scalarCDFOverlap β (cdf (μ : Measure ℝ)) q=q := by
  have hs := scalarCDFParisi_support_minima hβ μ hμ hmin q hqs
  have ha (x : ℝ) : cdf (μ : Measure ℝ) x∈Icc (0:ℝ) 1 := ⟨cdf_nonneg _ _,cdf_le_one _ _⟩
  by_cases hq0 : q=0
  · subst q
    exact scalarCDFOverlap_zero β ha (cdf (μ : Measure ℝ)).mono
  by_cases hq1 : q=1
  · subst q
    have HC := scalarCDFOverlap_continuousOn β (cdf (μ : Measure ℝ)) ha
      (supported_probability_cdf_one μ hμ)
    have HD := derivative_nonpos_at_right_minimum (scalarCDFPotential_hasDerivAt HC 1) hs.2.2
    rw [cdfGradientTest_eq ⟨zero_le_one,le_rfl⟩] at HD
    have HB := scalarCDFOverlap_nonneg_le_one β ha (cdf (μ : Measure ℝ)).mono
      (show (1:ℝ)∈Icc (0:ℝ) 1 from ⟨zero_le_one,le_rfl⟩)
    linarith [HB.2]
  · exact scalarCDFParisi_overlap_on_interior_support hβ μ hμ hmin hqs
      ⟨lt_of_le_of_ne hs.1.1 (Ne.symm hq0),lt_of_le_of_ne hs.1.2 hq1⟩

theorem scalarCDFParisi_overlap_eq_ae {β : ℝ} (hβ : β≠0)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β) :
    ∀ᵐ q ∂(μ : Measure ℝ), scalarCDFOverlap β (cdf (μ : Measure ℝ)) q=q := by
  have H : ∀ᵐ q ∂(μ : Measure ℝ), q∈(μ : Measure ℝ).support := (μ : Measure ℝ).support_mem_ae
  exact H.mono (fun _ hq => scalarCDFParisi_overlap_on_support hβ μ hμ hmin hq)

theorem supported_cdf_area (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1) :
    (∫ s in Icc (0:ℝ) 1, cdf (μ : Measure ℝ) s)=1-∫ q, q ∂(μ : Measure ℝ) := by
  have H := supported_cdf_integral_duality μ hμ (g:=fun _ => (1:ℝ)) (integrable_const 1)
  simp only [mul_one,intervalIntegral.integral_const,smul_eq_mul] at H
  have HI : Integrable (fun q : ℝ => q) (μ : Measure ℝ) :=
    supported_continuous_integrable μ hμ continuousOn_id
  rw [H,integral_sub (integrable_const 1) HI]
  simp only [integral_const,probReal_univ,one_smul]

end SK.Analytic

end
end

end OAI
