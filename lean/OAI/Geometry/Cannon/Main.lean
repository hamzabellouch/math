import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.HomeoPlane
import OAI.Geometry.Cannon.Boundary.BoundaryUniformComplementGraph
import OAI.Geometry.Cannon.Boundary.BoundaryUniformConnectedComplement
import OAI.Geometry.Cannon.PlaneTopology.ChartTameFaceCount
import OAI.Geometry.Cannon.PlaneTopology.BoundaryBallCover
import OAI.Geometry.Cannon.PlaneTopology.InteriorRadiusControl
import OAI.Geometry.Cannon.Boundary.BoundaryUniformRingPacking
import OAI.Geometry.Cannon.Uniformization.BoundaryUniformizationInputs
import OAI.Geometry.Cannon.Conformal.QuasiMobius
import OAI.Geometry.Cannon.Conformal.PlaneWeakQSBounded
import OAI.Geometry.Cannon.Actions.BoundaryAction

namespace OAI

/-! A group with a hyperbolic Cayley graph and spherical boundary admits a proper, cocompact action on hyperbolic three-space with finite kernel. -/

section
noncomputable section
namespace CannonRelease
universe u

theorem cannon (G : Type u) [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (D : CayleyData G) (hthin : D.ThinTriangles)
    (hsphere : Nonempty (Boundary D ≃ₜ SphereTwo)) :
    ∃ ρ : G →* H3Isom, ProperAction ρ ∧ CocompactAction ρ ∧
      (ρ.ker : Set G).Finite := by
  obtain ⟨δ,hδ⟩ := hthin
  obtain ⟨φ⟩ := hsphere
  let _ := visualMetricSpace D hδ
  obtain ⟨ψ,hψ⟩ := boundary_quasiMobius_uniformizer D hδ φ
  exact boundary_uniformized_action D hδ ψ hψ
end CannonRelease

end
end

end OAI
