import OAI.GroupTheory.PolycyclicRecognition.Algebra.LeftInvariantRiemannianDistance
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RiemannianChartLength
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

/-! # Local Lipschitz control of a chart by the Riemannian distance -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Manifold Bundle Metric
open scoped Topology Manifold ContDiff Bundle NNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ∞ G]
  [T3Space G] [ConnectedSpace G] (e : E ≃L[ℝ] F)

theorem leftRiemannianChart_lipschitz (x : G) :
    letI := leftRiemannianMetric (G := G) e
    ∃ C : ℝ≥0, ∃ U ∈ 𝓝 x,
      LipschitzOnWith C (extChartAt (𝓘(ℝ, E)) x) U := by
  let metric := leftRiemannianMetric (G := G) e
  let bundle := leftRiemannianBundle (G := G) e
  let continuousBundle : IsContinuousRiemannianBundle E
      (TangentSpace (𝓘(ℝ, E)) : G → Type _) :=
    ⟨⟨(leftInvariantRiemannianMetric (G := G) e).inner,
      (leftInvariantRiemannianMetric (G := G) e).contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  obtain ⟨C, hCpos, hC⟩ := eventually_enorm_mfderiv_extChartAt_lt (𝓘(ℝ, E)) x
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hC (chart_source_mem_nhds E x))
  have hpos : (0 : ℝ) < C := hCpos
  refine ⟨C, ball x (r / 4), ball_mem_nhds x (by positivity),
    LipschitzOnWith.of_dist_le_mul ?_⟩
  intro y hy z hz
  have hxy : dist x y < r / 4 := by simpa only [mem_ball, dist_comm] using hy
  have hxz : dist x z < r / 4 := by simpa only [mem_ball, dist_comm] using hz
  have hyz : dist y z < r / 2 := by
    have := dist_triangle y x z
    rw [dist_comm y x] at this
    linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := min (ε / (C : ℝ)) (r / 4)
  have hδ : 0 < δ := lt_min (div_pos hε hpos) (by positivity)
  have hδr : δ ≤ r / 4 := min_le_right _ _
  have hδε : (C : ℝ) * δ ≤ ε := by
    have := min_le_left (ε / (C : ℝ)) (r / 4)
    change δ ≤ ε / (C : ℝ) at this
    have h := (le_div_iff₀ hpos).mp this
    simpa only [mul_comm] using h
  have hnear : riemannianEDist (𝓘(ℝ, E)) y z < ENNReal.ofReal (dist y z + δ) := by
    change edist y z < _
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg]
    linarith
  obtain ⟨γ, h₀, h₁, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hnear
  have hfinite : pathELength (𝓘(ℝ, E)) γ 0 1 ≠ ⊤ := ne_top_of_lt hlen
  have hlenreal : (pathELength (𝓘(ℝ, E)) γ 0 1).toReal < dist y z + δ := by
    have h := (ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).mpr hlen
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ dist y z + δ)] using h
  have hinside (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ ball x r := by
    have hprefix : edist y (γ t) ≤ pathELength (𝓘(ℝ, E)) γ 0 1 :=
      (riemannianEDist_le_pathELength (hγ.mono (Icc_subset_Icc le_rfl ht.2))
        h₀ rfl ht.1).trans (pathELength_mono le_rfl ht.2)
    have hd := ENNReal.toReal_mono hfinite hprefix
    rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg] at hd
    rw [mem_ball, dist_comm]
    have htri := dist_triangle x y (γ t)
    linarith
  have hchart := chart_edist_le_pathELength x γ hγ
    (fun t ht => (hball (hinside t ht)).2) C
    (fun t ht => (hball (hinside t ht)).1.le)
  rw [h₀, h₁] at hchart
  have hchartreal := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hfinite) hchart
  rw [edist_dist, ENNReal.toReal_ofReal dist_nonneg, ENNReal.toReal_mul,
    ENNReal.coe_toReal] at hchartreal
  nlinarith

end PolycyclicRecognition

end

end OAI
