import OAI.Geometry.SurfaceImmersion.Geometry.HalfLinePuncturedNeighborhood
import OAI.Geometry.SurfaceImmersion.Geometry.BoundaryIncidentPiece

namespace OAI

/-! Boundary vertices of the actual finite decomposition have exactly
one incident open edge. -/
noncomputable section
open Set Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem boundary_vertex_degree_one (V : Set X) (hV : V.Finite) (P : Finset (Set X))
    (hP : ∀ E ∈ P, IsOpen E ∧ Disjoint E V ∧ closure E \ E ⊆ V)
    (hdis : ∀ E ∈ P, ∀ F ∈ P, E ≠ F → Disjoint E F)
    (hcover : Vᶜ = ⋃ E ∈ P, E) {p : X} (hp : p ∈ V)
    (c : OpenPartialHomeomorph X (Ici (0:ℝ))) (hc : p ∈ c.source)
    (hc0 : c p = ⟨0,by simp⟩) :
    ∃ E ∈ P, p ∈ closure E ∧ ∀ F ∈ P, p ∈ closure F → F = E := by
  obtain ⟨W,hW,hpW,hS,hSV,hpS⟩ := half_line_punctured_neighborhood c hc hc0 V hV
  exact unique_boundary_incident_piece V P hP hdis hcover hp hW hpW hS hSV hpS

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
