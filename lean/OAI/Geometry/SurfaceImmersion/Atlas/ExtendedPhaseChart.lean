import OAI.Geometry.SurfaceImmersion.Correction.SmoothPhaseChart
import OAI.Geometry.Immersion.ClosedSurface.LocalPhaseData

namespace OAI

/-! Smooth extensions of local phase coordinates on smaller neighborhoods. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

/-- Shrinking a smooth local chart lets its inverse be represented by an
actual globally smooth function, as needed by the supported mode solver. -/
theorem extend_local_chart_inverse (e : OpenPartialHomeomorph Base Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {p : Base} (hp : p ∈ e.source) :
    ∃ d : OpenPartialHomeomorph Base Base, p ∈ d.source ∧
      (d : Base → Base) = e ∧ d.source ⊆ e.source ∧ d.target ⊆ e.target ∧
      ContDiff ℝ ∞ d ∧ ContDiff ℝ ∞ d.symm := by
  obtain ⟨B,hB,_,_,hEq⟩ := smooth_extension_near e.open_target hi.contMDiffOn (e.map_source hp)
  have hN : {y : Base | B y = e.symm y} ∩ e.target ∈ 𝓝 (e p) :=
    inter_mem hEq (e.open_target.mem_nhds (e.map_source hp))
  obtain ⟨V,hV,hVo,hVp⟩ := mem_nhds_iff.mp hN
  have hvEq {y : Base} (hy : y ∈ V) : B y = e.symm y := (hV hy).1
  let d : OpenPartialHomeomorph Base Base := {
    toFun := e
    invFun := B
    source := e.source ∩ e ⁻¹' V
    target := e.target ∩ V
    map_source' := fun x hx => ⟨e.map_source hx.1,hx.2⟩
    map_target' := by
      intro y hy
      rw [hvEq hy.2]
      refine ⟨e.map_target hy.1,?_⟩
      change e (e.symm y) ∈ V
      simpa only [e.right_inv hy.1] using hy.2
    left_inv' := by
      intro x hx
      rw [hvEq hx.2]
      exact e.left_inv hx.1
    right_inv' := by
      intro y hy
      rw [hvEq hy.2]
      exact e.right_inv hy.1
    open_source := e.open_source.inter (hVo.preimage he.continuous)
    open_target := e.open_target.inter hVo
    continuousOn_toFun := he.continuous.continuousOn
    continuousOn_invFun := hB.contDiff.continuous.continuousOn
  }
  exact ⟨d,⟨hp,hVp⟩,rfl,fun _ h => h.1,fun _ h => h.1,he,hB.contDiff⟩

/-- Every noncritical phase admits the globally smooth representatives used
by local polynomial cancellation. This is a geometric construction. -/
theorem exists_extended_phase_chart {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {p : Base} (hp : phaseDerivative φ p ≠ 0) :
    ∃ e : OpenPartialHomeomorph Base Base, p ∈ e.source ∧
      (∀ x, (e x).1 = φ x) ∧ ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm := by
  obtain ⟨e,hep,hphase,he,hi⟩ := exists_smooth_phase_chart hφ hp
  obtain ⟨d,hdp,hde,_,_,hd,hdi⟩ := extend_local_chart_inverse e he hi hep
  exact ⟨d,hdp,fun x => by rw [hde]; exact hphase x,hd,hdi⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
