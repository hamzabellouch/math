import OAI.Geometry.SurfaceImmersion.Atlas.CompactPhaseDiskTopology
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseBoundaryCurve
import OAI.Geometry.SurfaceImmersion.Atlas.PreferredNormalPhasePullback

namespace OAI

/-! Transfer the preserved normal condition on the actual boundary curve
to the frontier of the disk in phase coordinates. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace PhaseBoundaryCurve
variable {B : SmoothingAtlas M} (c : PhaseBoundaryCurve B)

lemma frontier_avoidance {D : Set M} (hD : IsOpen D)
    (hDs : closure D ⊆ (surfacePhaseChart (c.index : M) c.phase).source)
    (hfront : c.carrier = frontier D)
    {F : M → Space} (n : PreferredNormal F)
    (hold : ∀ p ∈ c.carrier, c.second F p ≠ 0 ∧
      spaceCoordinates (n.vector p) ≠ -normalize (c.second F p)) :
    ∀ x ∈ frontier ((surfacePhaseChart (c.index : M) c.phase) '' D),
      realSecondForm (B.phaseRealChartMap c.index c.phase.symm F) dy dy x ≠ 0 ∧
      normalize (realSecondForm (B.phaseRealChartMap c.index c.phase.symm F) dy dy x) ≠
        -n.inPhase (c.index : M) c.phase x := by
  let E := surfacePhaseChart (c.index : M) c.phase
  have hK : IsCompact (closure D) := isClosed_closure.isCompact
  have h := compact_phase_disk_geometry E hD hK hDs
  intro x hx
  rw [h.2.2.1] at hx
  obtain ⟨p,hp,rfl⟩ := hx
  have hpc : p ∈ c.carrier := hfront.symm ▸ hp
  have hsec : c.second F p = realSecondForm (B.phaseRealChartMap c.index c.phase.symm F)
      dy dy (E p) := c.second_eq F hpc
  have hn : n.inPhase (c.index : M) c.phase (E p) = spaceCoordinates (n.vector p) := by
    change spaceCoordinates (n.vector (E.symm (E p))) = _
    rw [E.left_inv (hDs (frontier_subset_closure hp))]
  rw [← hsec,hn]
  refine ⟨(hold p hpc).1,?_⟩
  intro he
  apply (hold p hpc).2
  rw [he,neg_neg]

end PhaseBoundaryCurve
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
