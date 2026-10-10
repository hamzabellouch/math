import OAI.Geometry.SurfaceImmersion.Atlas.ExtendedPhaseChart
import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs

namespace OAI

/-! A single smooth inverse representative on a neighborhood of a compact
phase-chart region, without changing its forward coordinate map. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

theorem extend_compact_chart_inverse (e : OpenPartialHomeomorph Base Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {K : Set Base} (hK : IsCompact K) (hKe : K ⊆ e.source) :
    ∃ d : OpenPartialHomeomorph Base Base, K ⊆ d.source ∧
      (d : Base → Base) = e ∧ d.source ⊆ e.source ∧ d.target ⊆ e.target ∧
      ContDiff ℝ ∞ d ∧ ContDiff ℝ ∞ d.symm := by
  obtain ⟨W,hW,hKW,hWe,B,hB,hBE⟩ := CollarVelocity.compact_smooth_extension
    (hK.image he.continuous) e.open_target (image_subset_iff.mpr (fun x hx => e.map_source (hKe hx))) hi
  let d : OpenPartialHomeomorph Base Base := {
    toFun := e
    invFun := B
    source := e.source ∩ e ⁻¹' W
    target := e.target ∩ W
    map_source' := fun x hx => ⟨e.map_source hx.1,hx.2⟩
    map_target' := by
      intro y hy
      rw [hBE hy.2]
      refine ⟨e.map_target hy.1,?_⟩
      change e (e.symm y) ∈ W
      simpa only [e.right_inv hy.1] using hy.2
    left_inv' := by
      intro x hx
      rw [hBE hx.2]
      exact e.left_inv hx.1
    right_inv' := by
      intro y hy
      rw [hBE hy.2]
      exact e.right_inv hy.1
    open_source := e.open_source.inter (hW.preimage he.continuous)
    open_target := e.open_target.inter hW
    continuousOn_toFun := he.continuous.continuousOn
    continuousOn_invFun := hB.continuous.continuousOn
  }
  exact ⟨d,fun x hx => ⟨hKe hx,hKW (mem_image_of_mem e hx)⟩,
    rfl,fun _ hx => hx.1,fun _ hx => hx.1,he,hB⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
