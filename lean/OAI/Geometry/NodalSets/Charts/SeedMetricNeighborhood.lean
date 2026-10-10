import OAI.Geometry.NodalSets.Charts.MetricJetAdmissibility
import OAI.Geometry.NodalSets.Elliptic.SeedRoundPatch

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Filter Set Metric
open scoped ContDiff RealInnerProductSpace Topology
noncomputable section

def roundMetricJet (y : BaseModel) : MetricJet BaseModel :=
  (roundChartMetric seedPoint y,fderiv ℝ (roundChartMetric seedPoint) y)

lemma roundMetricJet_continuous : Continuous roundMetricJet :=
  (roundChartMetric_smooth seedPoint).continuous.prodMk
    ((roundChartMetric_smooth seedPoint).continuous_fderiv (by simp))

lemma seed_jet_admissible_center : JetAdmissible seedRealChart (roundMetricJet 0) 0 := by
  obtain ⟨hp,t,hpt,htt,_,hs⟩ := seed_round_admissibility
  exact ⟨hp,t,hpt,htt,hs⟩

lemma seed_jet_admissible_near_center :
    ∀ᶠ z : MetricJet BaseModel × BaseModel in 𝓝 (roundMetricJet 0,0),
      JetAdmissible seedRealChart z.1 z.2 := by
  apply jetAdmissible_eventually _ _ _ seedRealChart_smoothAt_zero _ seed_jet_admissible_center
  intro v hv
  change 0 < roundChartMetric seedPoint 0 v v
  rw [roundChartMetric_center]
  exact real_inner_self_pos.mpr hv

theorem seed_uniform_metric_neighborhood : ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧
    IsCompact (closedBall (0 : BaseModel) r) ∧
    (∀ y ∈ closedBall (0 : BaseModel) r,
      seedChartAmbient y ∈ seedLogDomain ∧ fderiv ℝ seedImagChart y ≠ 0) ∧
    ∀ g : BaseModel → BaseModel →L[ℝ] BaseModel →L[ℝ] ℝ,
      (∀ y ∈ closedBall (0 : BaseModel) r,
        dist ((g y,fderiv ℝ g y) : MetricJet BaseModel) (roundMetricJet y) < δ) →
      ∀ y ∈ closedBall (0 : BaseModel) r,
        JetAdmissible seedRealChart (g y,fderiv ℝ g y) y := by
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp seed_jet_admissible_near_center
  have hnear : ∀ᶠ y in 𝓝 (0 : BaseModel), dist (roundMetricJet y) (roundMetricJet 0) < ε/2 :=
    roundMetricJet_continuous.continuousAt.preimage_mem_nhds (ball_mem_nhds _ (by positivity))
  obtain ⟨a,ha,hasub⟩ := Metric.mem_nhds_iff.mp hnear
  obtain ⟨b,hb,_,hbprop⟩ := seed_round_compact_patch
  let r : ℝ := min (a/2) (min (ε/2) b)
  have hr : 0 < r := lt_min (by positivity) (lt_min (by positivity) hb)
  have hra : r < a := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hre : r < ε := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
  have hrb : r ≤ b := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r,ε/2,hr,by positivity,isCompact_closedBall _ _,?_,?_⟩
  · intro y hy
    exact (hbprop y (closedBall_subset_closedBall hrb hy)).imp_right And.left
  · intro g hg y hy
    apply hεsub (a := (((g y,fderiv ℝ g y) : MetricJet BaseModel),y))
    rw [mem_ball,Prod.dist_eq]
    apply max_lt
    · have hround := hasub (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hy) hra))
      change dist (roundMetricJet y) (roundMetricJet 0) < ε/2 at hround
      exact lt_of_le_of_lt (dist_triangle _ (roundMetricJet y) _)
        (by dsimp only; linarith [hg y hy])
    · exact lt_of_le_of_lt (mem_closedBall.mp hy) hre

end
end Yau.Target

end OAI
