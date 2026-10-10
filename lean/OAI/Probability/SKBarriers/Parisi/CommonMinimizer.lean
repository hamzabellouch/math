import Mathlib
import OAI.Probability.SKBarriers.Scalar.FullTimeSusceptibility
import OAI.Probability.SKBarriers.Parisi.CDFOriginStability
import OAI.Probability.SKBarriers.Parisi.CDFUpperArea

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFSusceptibilityAverage_zero (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α) :
    scalarCDFSusceptibilityAverage β α 0=scalarCDFHessian β α 0 1 0 := by
  have HE := scalarCDFAverage_eq_chainAverage_lipschitz
    (scalarCDFValue_regular β hα hmono 0 1 le_rfl)
    (scalarCDFValue_lipschitz β hα hmono 0 1 le_rfl)
    (scalarCDFHessian_lipschitz β hα hmono 0 1 le_rfl)
    (B:=1) (scalarCDFHessian_abs_le_one β hα hmono 0 1 le_rfl)
    β hα hmono [] (by simp) 0 0 (by norm_num) rfl trivial 0
  simpa only [scalarCDFSusceptibilityAverage,sub_zero,Real.toNNReal_one,Real.toNNReal_zero,
    scalarTimeChainAverage,List.length_nil,scalarHierarchyAverage] using HE

theorem exists_scalarCDFParisi_minimizer_locking_data {β : ℝ} (hβ : β≠0) :
    ∃ μ : ProbabilityMeasure ℝ, (μ : Measure ℝ) (Icc (0:ℝ) 1)=1 ∧
      scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β ∧
      (0:ℝ)∈(μ : Measure ℝ).support ∧
      scalarCDFHessian β (cdf (μ : Measure ℝ)) 0 1 0=
        (∫ s in (0:ℝ)..1, cdf (μ : Measure ℝ) s) ∧
      |β| *(∫ s in (0:ℝ)..1, cdf (μ : Measure ℝ) s) ≤ 1 ∧
      (∀ h : ℝ, 0<h → (∫ s in h..1, cdf (μ : Measure ℝ) s)<
        (∫ s in (0:ℝ)..1, cdf (μ : Measure ℝ) s)) ∧
      (∀ r∈Icc (0:ℝ) 1, scalarCDFSusceptibilityAverage β (cdf (μ : Measure ℝ)) r=
        (∫ s in r..1,cdf (μ : Measure ℝ) s)+cdf (μ : Measure ℝ) r*
          (r-scalarCDFOverlap β (cdf (μ : Measure ℝ)) r)) := by
  obtain ⟨μ,hμ,hm,hs⟩ := exists_scalarCDFParisi_minimizer_full_susceptibility β
  have h0 := scalarCDFParisi_zero_mem_support hβ μ hμ hm
  have hA (r : ℝ) (hr : r∈Icc (0:ℝ) 1) := scalarCDFParisi_susceptibility_area hβ μ hμ hm hs hr
  have ha (z : ℝ) : cdf (μ : Measure ℝ) z∈Icc (0:ℝ) 1 := ⟨cdf_nonneg _ _,cdf_le_one _ _⟩
  have hArea : scalarCDFHessian β (cdf (μ : Measure ℝ)) 0 1 0=
      (∫ s in (0:ℝ)..1,cdf (μ : Measure ℝ) s) := by
    have H := hA 0 ⟨le_rfl,zero_le_one⟩
    simpa only [scalarCDFSusceptibilityAverage_zero β ha (cdf (μ : Measure ℝ)).mono,
      scalarCDFOverlap_zero β ha (cdf (μ : Measure ℝ)).mono,sub_self,mul_zero,add_zero] using H
  refine ⟨μ,hμ,hm,h0,hArea,?_,fun h hh => cdf_area_strict μ h0 hh,fun r hr => hA r hr⟩
  have HS := scalarCDFParisi_origin_stability hβ μ hμ hm
  rw [hArea] at HS
  have HB := (sq_le_one_iff_abs_le_one (β*(∫ s in (0:ℝ)..1,cdf (μ : Measure ℝ) s))).mp
    (by simpa only [mul_pow] using HS)
  have hnonneg : 0≤∫ s in (0:ℝ)..1,cdf (μ : Measure ℝ) s :=
    intervalIntegral.integral_nonneg zero_le_one (fun s _ => cdf_nonneg _ s)
  simpa only [abs_mul,abs_of_nonneg hnonneg] using HB

end SK.Analytic

end
end

end OAI
