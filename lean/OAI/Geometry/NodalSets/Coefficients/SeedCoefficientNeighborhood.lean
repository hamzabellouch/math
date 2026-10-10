import OAI.Geometry.NodalSets.Coefficients.RoundCoefficientJets

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Filter Set Metric
open scoped ContDiff RealInnerProductSpace Topology
noncomputable section

lemma seed_coefficient_admissible_near_center :
    ∀ᶠ z : CoefficientFirstJet BaseModel × BaseModel in 𝓝 (roundCoefficientJet 0,0),
      JetAdmissible seedRealChart (coefficientMetricJet z.1) z.2 := by
  have hc := coefficientMetricJet_continuousAt (roundCoefficientJet 0)
    (positiveMetricEquiv _ (roundChartMetric_positive 0)).symm (roundCoefficient_inverse 0)
  have h : ContinuousAt (fun z : CoefficientFirstJet BaseModel × BaseModel ↦
      (coefficientMetricJet z.1,z.2)) (roundCoefficientJet 0,0) := by
    have hcf : ContinuousAt (fun z : CoefficientFirstJet BaseModel × BaseModel ↦ coefficientMetricJet z.1)
        (roundCoefficientJet 0,0) := by
      apply ContinuousAt.comp (f := fun z : CoefficientFirstJet BaseModel × BaseModel ↦ z.1)
        (x := (roundCoefficientJet 0,(0:BaseModel))) (g := coefficientMetricJet (E := BaseModel))
      · exact hc
      · exact continuousAt_fst
    exact hcf.prodMk continuousAt_snd
  have he : ∀ᶠ z : MetricJet BaseModel × BaseModel in
      𝓝 (coefficientMetricJet (roundCoefficientJet 0),0), JetAdmissible seedRealChart z.1 z.2 := by
    rw [roundCoefficientJet_metric]
    exact seed_jet_admissible_near_center
  exact h.tendsto.eventually he

theorem seed_uniform_coefficient_neighborhood : ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧
    IsCompact (closedBall (0 : BaseModel) r) ∧
    (∀ y ∈ closedBall (0 : BaseModel) r,
      seedChartAmbient y ∈ seedLogDomain ∧ fderiv ℝ seedImagChart y ≠ 0) ∧
    ∀ c : BaseModel → CoefficientPoint BaseModel,
      (∀ y ∈ closedBall (0 : BaseModel) r,
        dist ((c y,fderiv ℝ c y) : CoefficientFirstJet BaseModel) (roundCoefficientJet y) < δ) →
      ∀ y ∈ closedBall (0 : BaseModel) r,
        JetAdmissible seedRealChart (coefficientMetricJet (c y,fderiv ℝ c y)) y := by
  have hev : {z : CoefficientFirstJet BaseModel × BaseModel |
      JetAdmissible seedRealChart (coefficientMetricJet z.1) z.2} ∈ 𝓝 (roundCoefficientJet 0,0) :=
    seed_coefficient_admissible_near_center
  obtain ⟨ε,hε,hεsub⟩ := (Metric.mem_nhds_iff (α := CoefficientFirstJet BaseModel × BaseModel)).mp hev
  have hnear : ∀ᶠ y in 𝓝 (0 : BaseModel), dist (roundCoefficientJet y) (roundCoefficientJet 0) < ε/2 :=
    roundCoefficientJet_continuous.continuousAt.preimage_mem_nhds (ball_mem_nhds _ (by positivity))
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
  · intro c hc y hy
    apply hεsub (a := (((c y,fderiv ℝ c y) : CoefficientFirstJet BaseModel),y))
    rw [mem_ball,Prod.dist_eq]
    apply max_lt
    · have hround := hasub (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hy) hra))
      change dist (roundCoefficientJet y) (roundCoefficientJet 0) < ε/2 at hround
      exact lt_of_le_of_lt (dist_triangle _ (roundCoefficientJet y) _)
        (by dsimp only; linarith [hc y hy])
    · exact lt_of_le_of_lt (mem_closedBall.mp hy) hre

end
end Yau.Target

end OAI
