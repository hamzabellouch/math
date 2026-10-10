import OAI.Analysis.RCDHeat.TestPlanContinuous

namespace OAI

/-! # Derivative bounds for actual Sobolev representatives along test plans

Gram coefficients need not be continuous on the space. Their absolutely
continuous representatives along almost every path retain both endpoints
and the relaxed-slope derivative bound.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem IsRelaxedSlope.testPlan_ae_sobolev_derivative (μ : Measure X)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {C : ℝ≥0∞} (hC : C≠∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {u G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ u G) :
    ∀ᵐ γ ∂π, ∃ f : ℝ → ℝ,
      AbsolutelyContinuousOnInterval f 0 1 ∧ f 0=u (γ 0) ∧ f 1=u (γ 1) ∧
      (f =ᵐ[volume.restrict (Icc (0:ℝ) 1)] fun t => u (geodesicExtension γ t)) ∧
      ∀ᵐ s : ℝ, s∈Ioo (0:ℝ) 1 → DifferentiableAt ℝ f s ∧
        |deriv f s|≤dist (γ 0) (γ 1)*G (geodesicExtension γ s) := by
  filter_upwards [hG.testPlan_ae_representative μ π hgeo hC hcomp hD,
    testPlan_eval_intervalIntegrable μ π hC hcomp G,
    testPlan_eval_nonneg μ π hcomp (hG.nonneg μ)] with γ hf hi hnon
  obtain ⟨f,hf,hq,heq,hbound⟩ := hf
  refine ⟨f,hf,?_,?_,heq,?_⟩
  · simpa [rationalTime] using hq (0:ℚ)
  · simpa [rationalTime] using hq (1:ℚ)
  · have hnon' : ∀ᵐ s : ℝ, s∈Icc (0:ℝ) 1 → 0≤G (geodesicExtension γ s) :=
      (ae_restrict_iff' measurableSet_Icc).mp hnon
    let v r := dist (γ 0) (γ 1)*G (geodesicExtension γ r)
    have hiv : IntervalIntegrable v volume 0 1 := hi.const_mul _
    filter_upwards [hf.ae_differentiableAt,hiv.ae_hasDerivAt_integral,hnon'] with s hd hp hn hs
    have hsc : s∈uIcc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using Ioo_subset_Icc_self hs
    have h0 : (0:ℝ)∈uIcc (0:ℝ) 1 := by simp
    refine ⟨hd hsc,?_⟩
    have hb : |deriv f s|≤|v s| := by
      apply abs_deriv_le_of_dist_domination (hd hsc).hasDerivAt (hp hsc 0 h0)
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
      have hst := hbound (⟨s,Ioo_subset_Icc_self hs⟩:Time) (⟨t,Ioo_subset_Icc_self ht⟩:Time)
      have hi0 (a : ℝ) (ha : a∈Icc (0:ℝ) 1) : IntervalIntegrable v volume 0 a := by
        apply hiv.mono_set
        rw [uIcc_of_le ha.1,uIcc_of_le zero_le_one]
        exact Icc_subset_Icc le_rfl ha.2
      simp only [Real.dist_eq]
      rw [abs_sub_comm (f s),abs_sub_comm (∫ r in (0:ℝ)..s, v r),
        intervalIntegral.integral_interval_sub_left (hi0 t (Ioo_subset_Icc_self ht))
          (hi0 s (Ioo_subset_Icc_self hs))]
      simpa only [Real.dist_eq,abs_sub_comm,v,intervalIntegral.integral_const_mul] using hst
    change |deriv f s|≤|dist (γ 0) (γ 1)*G (geodesicExtension γ s)| at hb
    rwa [abs_of_nonneg (mul_nonneg dist_nonneg (hn (Ioo_subset_Icc_self hs)))] at hb

end RegularPointCoordinates

end

end OAI
