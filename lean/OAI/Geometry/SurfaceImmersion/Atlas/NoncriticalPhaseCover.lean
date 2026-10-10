import OAI.Geometry.SurfaceImmersion.Atlas.ExtendedPhaseChart
import OAI.Geometry.SurfaceImmersion.Atlas.CompactPhasePartition

namespace OAI

/-! Compact phase-chart geometry chosen independently of the immersion. -/
noncomputable section
open Set Filter TopologicalSpace
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

structure NoncriticalPhaseChart (φ : Base → ℝ) where
  chart : OpenPartialHomeomorph Base Base
  phase : ∀ x, (chart x).1 = φ x
  smooth : ContDiff ℝ ∞ chart
  smoothInverse : ContDiff ℝ ∞ chart.symm
  sourceCompact : Compacts Base
  targetCompact : Compacts Base
  sourceBound : chart.source ⊆ sourceCompact
  targetBound : chart.target ⊆ targetCompact

 theorem exists_noncriticalPhaseChart {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {p : Base} (hp : phaseDerivative φ p ≠ 0) :
    ∃ c : NoncriticalPhaseChart φ, p ∈ c.chart.source := by
  obtain ⟨e,hep,hphase,he,hi⟩ := exists_extended_phase_chart hφ hp
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp e.open_source p hep
  let V := Metric.ball p (r/2)
  let KE := Metric.closedBall p (r/2)
  have hKE : IsCompact KE := isCompact_closedBall p (r/2)
  let KV := e '' KE
  have hKV : IsCompact KV := hKE.image he.continuous
  let d := e.restrOpen V Metric.isOpen_ball
  refine ⟨⟨d,hphase,he,hi,⟨KE,hKE⟩,⟨KV,hKV⟩,?_,?_⟩,?_⟩
  · intro x hx
    exact Metric.ball_subset_closedBall hx.2
  · intro y hy
    refine ⟨d.symm y,Metric.ball_subset_closedBall (d.map_target hy).2,?_⟩
    exact d.right_inv hy
  · exact ⟨hep,Metric.mem_ball_self (by linarith)⟩

 theorem finite_noncritical_phase_cover {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (K : Compacts Base) (hφK : ∀ p ∈ (K : Set Base), phaseDerivative φ p ≠ 0) :
    ∃ (t : Finset K) (c : t → NoncriticalPhaseChart φ),
      (K : Set Base) ⊆ ⋃ i : t, (c i).chart.source := by
  classical
  choose c hc using fun p : K => exists_noncriticalPhaseChart hφ (hφK p p.property)
  have hcover : (K : Set Base) ⊆ ⋃ p : K, (c p).chart.source := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p,hp⟩,hc ⟨p,hp⟩⟩
  obtain ⟨t,ht⟩ := K.isCompact.elim_finite_subcover (fun p : K => (c p).chart.source)
    (fun p => (c p).chart.open_source) hcover
  refine ⟨t,fun i => c i.val,?_⟩
  intro p hp
  obtain ⟨i,hit,hi⟩ := mem_iUnion₂.mp (ht hp)
  exact mem_iUnion.mpr ⟨⟨i,hit⟩,hi⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
