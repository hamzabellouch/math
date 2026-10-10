import Mathlib
import OAI.Geometry.HyperbolicGroups.TreeCentroidCut

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
attribute [local instance] Classical.propDecidable
open SimpleGraph
variable {V : Type*}

lemma deleteIncidence_reachable_center_iff (G : SimpleGraph V) (v w : V) :
    (G.deleteIncidenceSet v).Reachable v w ↔ v = w := by
  constructor
  · rintro ⟨p⟩
    cases p with
    | nil => rfl
    | cons h p => exact ((deleteIncidenceSet_adj.mp h).2.1 rfl).elim
  · rintro rfl; exact .rfl

lemma deleteIncidence_center_component_iff (G : SimpleGraph V) (v w : V) :
    (G.deleteIncidenceSet v).connectedComponentMk w =
      (G.deleteIncidenceSet v).connectedComponentMk v ↔ w = v := by
  constructor
  · intro h
    exact ((deleteIncidence_reachable_center_iff G v w).mp
      (ConnectedComponent.exact h.symm)).symm
  · rintro rfl; rfl

variable [Fintype V] [DecidableEq V]

/-- Actual components after deleting a weighted tree centroid carry at most
half the total mass. The isolated centroid component is explicitly excluded. -/
theorem weighted_tree_component_separator (G : SimpleGraph V) (hG : G.IsTree)
    (weight : V → ℝ) (hw : ∀ x, 0 ≤ weight x) :
    ∃ v : V, ∀ C : (G.deleteIncidenceSet v).ConnectedComponent,
      C ≠ (G.deleteIncidenceSet v).connectedComponentMk v →
      2 * ∑ x ∈ C.supp.toFinset, weight x ≤ ∑ x : V, weight x := by
  classical
  obtain ⟨v,hv⟩ := weighted_tree_vertex_separator G hG weight hw
  refine ⟨v,?_⟩
  intro C hC
  have hnot : v ∉ C.supp := fun h => hC h.symm
  apply hv C.supp.toFinset
  · simpa only [Set.mem_toFinset] using hnot
  · have hc := C.connected_toSimpleGraph.preconnected
    change ((G.deleteIncidenceSet v).induce C.supp).Preconnected at hc
    rw [G.induce_deleteIncidenceSet_of_notMem hnot] at hc
    have he : (C.supp.toFinset : Set V) = C.supp := Set.coe_toFinset C.supp
    rw [he]
    exact hc

end HyperbolicObstruction.PlanarRecursion
end
end

section

end
end

end OAI
