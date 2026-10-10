import Mathlib
import OAI.Probability.SKBarriers.Scalar.SuffixPartitionSusceptibility
import OAI.Probability.SKBarriers.Parisi.CDFSupportContact

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem supported_cdf_upper_area (μ : ProbabilityMeasure ℝ)
    (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1) {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    (∫ s in r..1, cdf (μ : Measure ℝ) s)=1-∫ q,max q r ∂(μ : Measure ℝ) := by
  have E : (fun p : ℝ×ℝ => unitCDF p.1 p.2)=
      {p : ℝ×ℝ | p.1≤p.2}.indicator (fun _ => (1:ℝ)) := by
    funext p
    simp only [unitCDF,indicator_apply,mem_ofPred_eq]
  have HI : Integrable (fun p : ℝ×ℝ => unitCDF p.1 p.2)
      ((μ : Measure ℝ).prod (volume.restrict (Icc r 1))) := by
    rw [E]
    exact (integrable_const 1).indicator (measurableSet_le measurable_fst measurable_snd)
  have H := integral_integral_swap (f:=fun q s => unitCDF q s) HI
  have hc (s : ℝ) : (∫ q,unitCDF q s ∂(μ : Measure ℝ))=cdf (μ : Measure ℝ) s := by
    simpa only [mul_one] using integral_unitCDF_probability μ s 1
  simp_rw [hc] at H
  rw [intervalIntegral.integral_of_le hr.2,← integral_Icc_eq_integral_Ioc,← H]
  have he : (∫ q, ∫ s in Icc r 1,unitCDF q s ∂volume ∂(μ : Measure ℝ))=
      ∫ q,1-max q r ∂(μ : Measure ℝ) := by
    apply integral_congr_ae
    filter_upwards [supported_probability_ae μ hμ] with q hq
    have E : (fun s => unitCDF q s)=(Ici q).indicator (fun _ => (1:ℝ)) := by
      simpa only [mul_one] using unitCDF_mul_indicator q (fun _ => (1:ℝ))
    rw [E,setIntegral_indicator measurableSet_Ici]
    have he : Icc r 1∩Ici q=Icc (max q r) 1 := by
      ext x; simp only [mem_inter_iff,mem_Icc,mem_Ici,max_le_iff]; tauto
    rw [he,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (max_le hq.2 hr.2)]
    simp
  have hM : Integrable (fun q : ℝ => max q r) (μ : Measure ℝ) :=
    supported_continuous_integrable μ hμ (continuous_id.max continuous_const).continuousOn
  rw [he,integral_sub (integrable_const 1) hM]
  simp

theorem scalarCDFParisi_susceptibility_area {β : ℝ} (hβ : β≠0)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β)
    (hs : ∀ r∈Icc (0:ℝ) 1, scalarCDFSusceptibilityAverage β (cdf (μ : Measure ℝ)) r=
      1-∫ x,scalarCDFOverlap β (cdf (μ : Measure ℝ)) (max x r) ∂(μ : Measure ℝ))
    {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    scalarCDFSusceptibilityAverage β (cdf (μ : Measure ℝ)) r=
      (∫ s in r..1,cdf (μ : Measure ℝ) s)+cdf (μ : Measure ℝ) r*
        (r-scalarCDFOverlap β (cdf (μ : Measure ℝ)) r) := by
  let Γ := scalarCDFOverlap β (cdf (μ : Measure ℝ))
  have he : (fun x => Γ (max x r))=ᵐ[(μ : Measure ℝ)]
      (fun x => max x r+(Iic r).indicator (fun _ => Γ r-r) x) := by
    filter_upwards [scalarCDFParisi_overlap_eq_ae hβ μ hμ hmin] with x hx
    by_cases hxr : x≤r
    · simp only [max_eq_right hxr,indicator_apply,mem_Iic,ite_eq_left hxr]
      ring
    · simp only [max_eq_left (le_of_not_ge hxr),indicator_apply,mem_Iic,ite_eq_right hxr,add_zero]
      exact hx
  have hM : Integrable (fun x : ℝ => max x r) (μ : Measure ℝ) :=
    supported_continuous_integrable μ hμ (continuous_id.max continuous_const).continuousOn
  rw [hs r hr,integral_congr_ae he,integral_add hM ((integrable_const (Γ r-r)).indicator measurableSet_Iic),
    integral_indicator measurableSet_Iic,setIntegral_const,supported_cdf_upper_area μ hμ hr,
    smul_eq_mul,← cdf_eq_real]
  dsimp [Γ]
  ring

end SK.Analytic

end
end

end OAI
