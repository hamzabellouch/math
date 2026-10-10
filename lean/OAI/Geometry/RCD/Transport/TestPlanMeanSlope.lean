import OAI.Geometry.RCD.Transport.TestPlanTemporalDifference
import OAI.Geometry.RCD.Transport.TestPlanIntervalFlux

namespace OAI

/-! # The spatial slope of a fixed Sobolev function along a plan -/

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (Q : QuadraticCheegerEnergy μ)
attribute [local instance] pathBorel pathBorelSpace

theorem testPlanMeanCLM_right_slope_bound (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hLength : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    (u : SobolevSpace μ Q) (s : Time) (hs : (s:ℝ) < 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝[>] (s:ℝ),
      |(testPlanMeanCLM μ π hC hcomp t (SobolevSpace.toLp μ Q u)-
        testPlanMeanCLM μ π hC hcomp s (SobolevSpace.toLp μ Q u))/(t-s)| <
      (∫ γ : C(Time,X), dist (γ 0) (γ 1)*SobolevSpace.minimalSlope μ Q u (γ s) ∂π)+ε := by
  have hb := (SobolevSpace.minimalSlope_isRelaxed μ Q u).testPlan_right_slope_bound
    μ π hgeo hC hcomp hLength s hs hε
  have hsmall : ∀ᶠ t in 𝓝[>] (s:ℝ), t < 1 :=
    (gt_mem_nhds hs).filter_mono nhdsWithin_le_nhds
  filter_upwards [hb,hsmall,self_mem_nhdsWithin] with t ht ht1 hts
  have h01 : t ∈ Icc (0:ℝ) 1 := ⟨s.2.1.trans hts.le,ht1.le⟩
  have hi (r : Time) : Integrable (fun γ : C(Time,X) => SobolevSpace.toLp μ Q u (γ r)) π :=
    (compressionPullback_memLp μ π _ (measurable_path_eval r) hC (hcomp r)
      (SobolevSpace.toLp μ Q u)).integrable (by norm_num)
  have he (γ : C(Time,X)) : geodesicExtension γ t = γ ⟨t,h01⟩ :=
    geodesicExtension_eq γ ⟨t,h01⟩
  rw [testPlanMeanCLM_apply,testPlanMeanCLM_apply]
  simp only [geodesicExtension_eq] at ⊢
  simp_rw [he] at ht ⊢
  rw [abs_div,show |t-(s:ℝ)| = t-s from abs_of_pos (sub_pos.mpr hts),
    ← integral_sub (hi ⟨t,h01⟩) (hi s)]
  exact (div_le_div_of_nonneg_right abs_integral_le_integral_abs (sub_nonneg.mpr hts.le)).trans_lt ht

end RegularPointCoordinates

end

end OAI
