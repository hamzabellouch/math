import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFCramer
import OAI.Probability.SKBarriers.Parisi.CDFZeroSupport
import OAI.Probability.SKBarriers.Parisi.CDFSusceptibilityIdentity

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem origin_coefficient_le_of_min {G Γ J : ℝ → ℝ} (hG : Continuous G)
    (hd : ∀ s∈Icc (0:ℝ) 1, HasDerivAt G (s-Γ s) s) (hJ : Continuous J)
    (hi : ∀ s∈Icc (0:ℝ) 1, s*J s ≤ Γ s)
    (hmin : ∀ r∈Icc (0:ℝ) 1, G 0 ≤ G r) : J 0 ≤ 1 := by
  by_contra H
  have hJ0 : 1 < J 0 := lt_of_not_ge H
  obtain ⟨ε,hε,hεJ⟩ := Metric.eventually_nhds_iff.mp (hJ.continuousAt.preimage_mem_nhds
    (Ioi_mem_nhds hJ0))
  let δ := min (1/2:ℝ) (ε/2)
  have hδ : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hδε : δ ≤ ε/2 := min_le_right _ _
  have hneg {s : ℝ} (hs : s∈Ioo (0:ℝ) δ) : s-Γ s < 0 := by
    have hsJ : 1 < J s := by
      apply hεJ
      rw [Real.dist_eq,sub_zero,abs_of_pos hs.1]
      linarith [hs.2]
    have H := hi s ⟨hs.1.le,hs.2.le.trans hδ1⟩
    nlinarith [mul_lt_mul_of_pos_left hsJ hs.1]
  have hstrict := strictAntiOn_of_deriv_neg (convex_Icc (0:ℝ) δ) hG.continuousOn
    (fun s hs => by
      rw [interior_Icc] at hs
      rw [(hd s ⟨hs.1.le,hs.2.le.trans hδ1⟩).deriv]
      exact hneg hs)
  exact (not_lt_of_ge (hmin δ ⟨hδ.le,hδ1⟩))
    (hstrict ⟨le_rfl,hδ.le⟩ ⟨hδ.le,le_rfl⟩ hδ)

theorem scalarCDFParisi_origin_stability {β : ℝ} (hβ : β≠0)
    (μ : ProbabilityMeasure ℝ) (hμ : (μ : Measure ℝ) (Icc (0:ℝ) 1)=1)
    (hmin : scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β) :
    β^2*(scalarCDFHessian β (cdf (μ : Measure ℝ)) 0 1 0)^2 ≤ 1 := by
  let α := cdf (μ : Measure ℝ)
  have ha (z : ℝ) : α z∈Icc (0:ℝ) 1 := ⟨cdf_nonneg _ _,cdf_le_one _ _⟩
  have h1 : α 1=1 := supported_probability_cdf_one μ hμ
  have hΓ := scalarCDFOverlap_continuousOn β α ha h1
  let χ := scalarCDFHessian β α 0 1 0
  let J (s : ℝ) := β^2*(max (χ-(s-cdfGradientTest β α s)) 0)^2
  have hJ : Continuous J := continuous_const.mul
    ((continuous_const.sub (continuous_id.sub (cdfGradientTest_continuous hΓ))).max continuous_const |>.pow 2)
  have H := origin_coefficient_le_of_min (scalarCDFPotential_continuous hΓ)
    (fun s hs => by simpa only [cdfGradientTest_eq hs] using scalarCDFPotential_hasDerivAt hΓ s) hJ
    (fun s hs => by
      have H := scalarCDFOverlap_cramer β α ha h1 hs
      dsimp [J]
      rw [cdfGradientTest_eq hs,sub_sub_cancel]
      nlinarith)
    ((scalarCDFParisi_support_minima hβ μ hμ hmin 0
      (scalarCDFParisi_zero_mem_support hβ μ hμ hmin)).2.2)
  have hχ : 0 ≤ χ := (scalarCDF_derivative_bounds β ha α.mono 0 1 le_rfl 0).2.1
  simpa only [J,cdfGradientTest_eq (show (0:ℝ)∈Icc (0:ℝ) 1 from ⟨le_rfl,zero_le_one⟩),
    scalarCDFOverlap_zero β ha α.mono,sub_zero,sub_self,max_eq_left hχ] using H

theorem exists_scalarCDFParisi_minimizer_stable_area {β : ℝ} (hβ : β≠0) :
    ∃ μ : ProbabilityMeasure ℝ, (μ : Measure ℝ) (Icc (0:ℝ) 1)=1 ∧
      scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β ∧
      (0:ℝ)∈(μ : Measure ℝ).support ∧
      scalarCDFHessian β (cdf (μ : Measure ℝ)) 0 1 0=
        (∫ s in (0:ℝ)..1, cdf (μ : Measure ℝ) s) ∧
      |β| *(∫ s in (0:ℝ)..1, cdf (μ : Measure ℝ) s) ≤ 1 ∧
      ∀ h : ℝ, 0<h → (∫ s in h..1, cdf (μ : Measure ℝ) s)<
        (∫ s in (0:ℝ)..1, cdf (μ : Measure ℝ) s) := by
  obtain ⟨μ,hμ,hm,he⟩ := exists_scalarCDFParisi_minimizer_area hβ
  have h0 := scalarCDFParisi_zero_mem_support hβ μ hμ hm
  have harea : scalarCDFHessian β (cdf (μ : Measure ℝ)) 0 1 0=
      (∫ s in (0:ℝ)..1, cdf (μ : Measure ℝ) s) := by
    rw [intervalIntegral.integral_of_le zero_le_one,← integral_Icc_eq_integral_Ioc]
    exact he
  refine ⟨μ,hμ,hm,h0,harea,?_,fun h hh => cdf_area_strict μ h0 hh⟩
  have HS := scalarCDFParisi_origin_stability hβ μ hμ hm
  rw [harea] at HS
  have HB := (sq_le_one_iff_abs_le_one (β*(∫ s in (0:ℝ)..1, cdf (μ : Measure ℝ) s))).mp
    (by simpa only [mul_pow] using HS)
  have hA : 0 ≤ ∫ s in (0:ℝ)..1, cdf (μ : Measure ℝ) s :=
    intervalIntegral.integral_nonneg zero_le_one (fun s _ => cdf_nonneg _ s)
  simpa only [abs_mul,abs_of_nonneg hA] using HB

end SK.Analytic

end
end

end OAI
