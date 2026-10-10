import OAI.Geometry.NodalSets.Charts.LocalMetricJetContinuityLemmas
import OAI.Geometry.NodalSets.Elliptic.SeedRoundAdmissibility
import OAI.Geometry.NodalSets.Persistence.LocalAdmissibilityPersistence

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Filter Set Metric
open scoped ContDiff RealInnerProductSpace Topology
noncomputable section

def seedChartAmbient : BaseModel → SeedAmbient := (Subtype.val : Base → SeedAmbient) ∘
  (extChartAt (𝓡 4) seedPoint).symm

lemma seedChartAmbient_smooth : ContDiff ℝ ∞ seedChartAmbient := by
  rw [show seedChartAmbient = stereoInvFunAux (-(seedPoint : SeedAmbient)) ∘ centeredSphereIsometry seedPoint from
    centeredSphereChart_inverse seedPoint]
  exact contDiff_stereoInvFunAux.comp (centeredSphereIsometry seedPoint).contDiff

lemma seedChartAmbient_zero : seedChartAmbient 0 = (seedPoint : SeedAmbient) :=
  congrArg (Subtype.val : Base → SeedAmbient) (centeredSphereChart_inverse_zero seedPoint)

lemma seedRealChart_smoothAt_zero : ContDiffAt ℝ ∞ seedRealChart 0 := by
  have hf := Complex.reCLM.contDiff.contDiffAt.comp _ (seedLog_contDiffAt seedPoint_mem_logDomain)
  rw [← seedChartAmbient_zero] at hf
  exact hf.comp 0 seedChartAmbient_smooth.contDiffAt

lemma seedImagChart_smoothAt_zero : ContDiffAt ℝ ∞ seedImagChart 0 := by
  have hf := Complex.imCLM.contDiff.contDiffAt.comp _ (seedLog_contDiffAt seedPoint_mem_logDomain)
  rw [← seedChartAmbient_zero] at hf
  exact hf.comp 0 seedChartAmbient_smooth.contDiffAt

lemma seedImagChart_differential_ne_zero : fderiv ℝ seedImagChart 0 ≠ 0 := by
  obtain ⟨t,ht⟩ := centeredSphereIsometry_exists seedPoint seedImagTestVector seedImagTest_tangent
  have h : fderiv ℝ seedImagChart 0 t = 3 := by
    rw [show seedImagChart = (fun x : Base ↦ seedLogImag x) ∘
      (extChartAt (𝓡 4) seedPoint).symm from rfl,
      seed_chart_first seedLogImag (seedLogImag_hasFDerivAt seedPoint_mem_logDomain).differentiableAt,
      ht,seedLog_imag_test]
  intro hz
  simp [hz] at h

def seedRoundAdmissible (y : BaseModel) : Prop :=
  let g := roundChartMetric seedPoint
  let p := localMetricGradient g seedRealChart y
  let H := localMetricHessian g seedRealChart y
  p ≠ 0 ∧ ∃ t : BaseModel, g y p t = 0 ∧ g y t t = 1 ∧
    0 < H p p + (g y p p+4)*H t t

lemma seedRoundAdmissible_eventually : ∀ᶠ y in 𝓝 (0 : BaseModel), seedRoundAdmissible y := by
  have hpos (v : BaseModel) (hv : v ≠ 0) : 0 < roundChartMetric seedPoint 0 v v := by
    rw [roundChartMetric_center]; exact real_inner_self_pos.mpr hv
  obtain ⟨hp,t,hpt,htt,_,hs⟩ := seed_round_admissibility
  exact admissibility_eventually (roundChartMetric seedPoint)
    (localMetricHessian (roundChartMetric seedPoint) seedRealChart)
    (localMetricGradient (roundChartMetric seedPoint) seedRealChart) 0
    (roundChartMetric_smooth seedPoint).continuous.continuousAt
    (localMetricHessian_continuousAt _ _ _ (roundChartMetric_smooth seedPoint).contDiffAt
      seedRealChart_smoothAt_zero hpos)
    (localMetricGradient_continuousAt _ _ _ (roundChartMetric_smooth seedPoint).continuous.continuousAt
      seedRealChart_smoothAt_zero hpos)
    (hpos _ hp) t hpt htt hs

theorem seed_round_compact_patch : ∃ r : ℝ, 0 < r ∧ IsCompact (closedBall (0 : BaseModel) r) ∧
    ∀ y ∈ closedBall (0 : BaseModel) r,
      seedChartAmbient y ∈ seedLogDomain ∧ fderiv ℝ seedImagChart y ≠ 0 ∧ seedRoundAdmissible y := by
  have hb : ∀ᶠ y in 𝓝 (0 : BaseModel), seedChartAmbient y ∈ seedLogDomain :=
    seedChartAmbient_smooth.continuous.continuousAt.preimage_mem_nhds
      (seedLogDomain_open.mem_nhds (by rw [seedChartAmbient_zero]; exact seedPoint_mem_logDomain))
  have hd : ∀ᶠ y in 𝓝 (0 : BaseModel), fderiv ℝ seedImagChart y ≠ 0 :=
    (seedImagChart_smoothAt_zero.continuousAt_fderiv (by simp)).eventually_ne
      seedImagChart_differential_ne_zero
  have hall := hb.and (hd.and seedRoundAdmissible_eventually)
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨r/2,by positivity,isCompact_closedBall _ _,?_⟩
  intro y hy
  apply hsub
  exact mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hy) (by linarith))

end
end Yau.Target

end OAI
