import OAI.Combinatorics.Crossing.ConnectorSupportingLines
import OAI.Combinatorics.Crossing.MovingDiskClearance

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
open scoped Topology
variable {m n : ℕ} {D : ContinuousDrawing m n} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

theorem exists_connector_other_disks_radius :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, |ε|<δ → ∀ j k, j ≠ k → ∀ f : IncidentEdges j,
      segment ℝ (C.shiftedPort j f ε) (C.tangentPort j f ε) ⊆
        {x | V.radius^2 < squaredLength (x-D.vertex k)} := by
  classical
  let Pair := Σ j : BipartiteVertex m n, Σ k : {k : BipartiteVertex m n // j ≠ k}, IncidentEdges j
  have hstart (b : Pair) : segment ℝ (C.shiftedPort b.1 b.2.2 0) (C.tangentPort b.1 b.2.2 0) ⊆
      {x | V.radius^2 < squaredLength (x-D.vertex b.2.1.val)} := by
    rw [C.shiftedPort_zero,C.tangentPort_zero,segment_same]
    intro x hx
    have he : x=V.spokePort b.1 b.2.2 := hx
    subst x
    change V.radius^2 < squaredLength (V.spokePort b.1 b.2.2-D.vertex b.2.1.val)
    by_contra hh
    have hj : V.spokePort b.1 b.2.2 ∈ closedRoundDisk (D.vertex b.1) V.radius := by
      change squaredLength (V.spokePort b.1 b.2.2-D.vertex b.1) ≤ V.radius^2
      rw [V.spokePort_circle]
    have hk : V.spokePort b.1 b.2.2 ∈ closedRoundDisk (D.vertex b.2.1.val) V.radius := not_lt.mp hh
    exact Set.disjoint_left.mp (V.disks_disjoint b.1 b.2.1.val b.2.1.property) hj hk
  have hevent (b : Pair) := eventually_moving_segment_outside_disk
    (C.shiftedPort b.1 b.2.2) (C.tangentPort b.1 b.2.2)
    (C.continuous_shiftedPort b.1 b.2.2) (C.continuous_tangentPort b.1 b.2.2)
    (D.vertex b.2.1.val) V.radius (hstart b)
  have hex (b : Pair) := Metric.eventually_nhds_iff.mp (hevent b)
  choose radius hpos hprop using hex
  obtain ⟨δ,hδ,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun b _ => hpos b)
  refine ⟨δ,hδ,?_⟩
  intro ε hε j k hjk f
  exact hprop ⟨j,⟨k,hjk⟩,f⟩ (by simpa [Real.dist_eq] using hε.trans (hbound ⟨j,⟨k,hjk⟩,f⟩ (Finset.mem_univ _)))

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
