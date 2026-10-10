import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.LocalDistance

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff ENNReal Manifold

namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
open NormalNeighborhood NormalFlow ChartMetric

 theorem uniform_normal_radius (x z₀ : M) (hz₀ : z₀ ∈ (chartAt E x).source)
    (N : NormalFlow (metric x) (chartAt E x).target (chartAt E x z₀)) :
    ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧ ∀ z ∈ Metric.ball z₀ ε,
      z ∈ (chartAt E x).source ∧
      (0 : E) ∈ (N.normalAt (chartAt E x z)).source ∧
      Metric.ball z r ⊆ (normalChart x z N).target := by
  let c := chartAt E x
  have hx : z₀ ∈ c.source := hz₀
  have hc : ContinuousAt c z₀ := c.continuousAt hx
  have hzero : N.normal (c z₀, 0) = (c z₀, c z₀) := by
    have hh := N.normalAt_zero c.open_target (metric_smooth x)
      (fun z hz v hv => metric_positive x hz hv) N.center_mem
    rw [N.normalAt_apply] at hh
    rw [N.normal_apply, hh]
  have hpair : (c z₀, c z₀) ∈ N.normal.target := by
    rw [← hzero]
    exact N.normal.map_source N.center_mem
  let A : Set M := c.source ∩ {z | (c z, (0 : E)) ∈ N.normal.source}
  have hA : A ∈ 𝓝 z₀ :=
    inter_mem (c.open_source.mem_nhds hx)
      ((hc.prodMk continuousAt_const).preimage_mem_nhds (N.normal.open_source.mem_nhds N.center_mem))
  let B : Set (M × M) := {q | q.1 ∈ c.source ∧ q.2 ∈ c.source ∧
    (c q.1, c q.2) ∈ N.normal.target}
  have hB : B ∈ 𝓝 (z₀, z₀) := by
    have h₁ : {q : M × M | q.1 ∈ c.source} ∈ 𝓝 (z₀, z₀) := continuousAt_fst.preimage_mem_nhds (c.open_source.mem_nhds hx)
    have h₂ : {q : M × M | q.2 ∈ c.source} ∈ 𝓝 (z₀, z₀) := continuousAt_snd.preimage_mem_nhds (c.open_source.mem_nhds hx)
    have hcc : ContinuousAt (fun q : M × M => (c q.1, c q.2)) (z₀, z₀) :=
      (hc.comp continuousAt_fst).prodMk (hc.comp continuousAt_snd)
    have h₃ := hcc.preimage_mem_nhds (N.normal.open_target.mem_nhds hpair)
    exact inter_mem h₁ (inter_mem h₂ h₃)
  obtain ⟨δ₁, hδ₁, hs₁⟩ := Metric.mem_nhds_iff.mp hA
  obtain ⟨δ₂, hδ₂, hs₂⟩ := Metric.mem_nhds_iff.mp hB
  refine ⟨min δ₁ (δ₂ / 3), δ₂ / 3, lt_min hδ₁ (by positivity), by positivity, ?_⟩
  intro z hz
  have hz₁ : dist z z₀ < δ₁ := lt_of_lt_of_le hz (min_le_left _ _)
  have hz₂ : dist z z₀ < δ₂ / 3 := lt_of_lt_of_le hz (min_le_right _ _)
  have ha := hs₁ hz₁
  refine ⟨ha.1, ha.2, ?_⟩
  intro y hy
  have hp : (z, y) ∈ Metric.ball (z₀, z₀) δ₂ := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · change dist z z₀ < δ₂
      linarith
    · change dist y z₀ < δ₂
      have hd := dist_triangle y z z₀
      change dist y z < δ₂ / 3 at hy
      linarith
  have hb := hs₂ hp
  exact ⟨hb.2.1, hb.2.2⟩

end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI
