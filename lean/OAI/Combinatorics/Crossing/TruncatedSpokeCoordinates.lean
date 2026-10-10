import OAI.Combinatorics.Crossing.TruncatedSpokeDirections
import OAI.Combinatorics.Crossing.TangentTrackIdentity

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D : ContinuousDrawing m n}

structure TruncatedSpokeCoordinates (V : VertexTruncation D) where
  frame : BipartiteVertex m n → Plane
  frame_ne_zero : ∀ j, frame j ≠ 0
  frame_length : ∀ j, squaredLength (frame j)=V.radius^2
  node : ∀ j, IncidentEdges j → ℝ
  node_injective : ∀ j, Function.Injective (node j)
  point_eq : ∀ j e, similarityPoint (D.vertex j) (frame j) (circlePoint (node j e))=V.spokePort j e

theorem nonempty_truncatedSpokeCoordinates {A : AdmissibleDrawing m n}
    (V : VertexTruncation A.toContinuousDrawing) (hnorm : NoAdjacentCrossings A) :
    Nonempty (TruncatedSpokeCoordinates V) := by
  have hex (j : BipartiteVertex m n) := exists_finite_circle_coordinates
    (A.vertex j) V.radius V.radius_pos (V.spokePort j)
    (V.spokePort_injective hnorm j) (V.spokePort_circle j)
  choose u hu hlen node hnode hpoint using hex
  exact ⟨⟨u,hu,hlen,node,hnode,hpoint⟩⟩

namespace TruncatedSpokeCoordinates
variable {V : VertexTruncation D} (C : TruncatedSpokeCoordinates V)

def shiftedPort (j : BipartiteVertex m n) (e : IncidentEdges j) (ε : ℝ) : Plane :=
  similarityPoint (D.vertex j) (C.frame j)
    (circleOffset (circlePoint (C.node j e)) (V.spokeScale j e*ε))

def tangentPort (_C : TruncatedSpokeCoordinates V) (j : BipartiteVertex m n) (e : IncidentEdges j) (ε : ℝ) : Plane :=
  V.spokePort j e+ε • normalShift (V.spokeDirection j e)

theorem tangentPort_eq (j : BipartiteVertex m n) (e : IncidentEdges j) (ε : ℝ) :
    C.tangentPort j e ε = similarityPoint (D.vertex j) (C.frame j)
      (circleTangentOffset (circlePoint (C.node j e)) (V.spokeScale j e*ε)) := by
  have hh := tangentOffset_eq_normalShift (D.vertex j) (C.frame j) (circlePoint (C.node j e))
    (V.spokeDirection j e) (V.spokeDirection_ne_zero j e)
    (by simpa only [C.point_eq] using V.spokePort_ne_center j e)
    (by simpa only [C.point_eq] using V.spokeDirection_parallel j e) ε
  simpa only [C.point_eq,VertexTruncation.spokeScale,tangentPort] using hh.symm

theorem shiftedPort_level (j : BipartiteVertex m n) (e : IncidentEdges j) (ε : ℝ) :
    det2 (V.spokeDirection j e) (C.shiftedPort j e ε-V.spokePort j e)=ε := by
  have hh := circleOffset_track_level (D.vertex j) (C.frame j) (circlePoint (C.node j e))
    (V.spokeDirection j e) (V.spokeDirection_ne_zero j e)
    (by simpa only [C.point_eq] using V.spokePort_ne_center j e)
    (by simpa only [C.point_eq] using V.spokeDirection_parallel j e) ε
  simpa only [C.point_eq,VertexTruncation.spokeScale,shiftedPort] using hh

theorem shiftedPort_circle (j : BipartiteVertex m n) (e : IncidentEdges j) (ε : ℝ)
    (hε : |V.spokeScale j e*ε| ≤ 1) :
    squaredLength (C.shiftedPort j e ε-D.vertex j)=V.radius^2 := by
  unfold shiftedPort
  rw [similarityPoint_squaredLength,circleOffset_on_circle _ (circlePoint_on_unit_circle _) _ hε,
    mul_one,C.frame_length]

theorem connector_strictly_outside (j : BipartiteVertex m n) (e : IncidentEdges j) (ε : ℝ)
    (hε : |V.spokeScale j e*ε| < 1) (hne : ε ≠ 0) (t : ℝ) (ht : 0<t) :
    V.radius^2 < squaredLength (segmentPoint (C.shiftedPort j e ε) (C.tangentPort j e ε) t-D.vertex j) := by
  rw [C.tangentPort_eq]
  have hh := physical_circleConnector_strictly_outside (D.vertex j) (C.frame j)
    (circlePoint (C.node j e)) (C.frame_ne_zero j) (circlePoint_on_unit_circle _)
    (V.spokeScale j e*ε) hε (mul_ne_zero (V.spokeScale_ne_zero j e) hne) t ht
  simpa only [C.frame_length,shiftedPort] using hh

theorem exists_vertex_average_radius (j : BipartiteVertex m n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ → ∀ a b c d : IncidentEdges j,
      a ≠ b → c ≠ d →
      (segmentCrossingSign (V.spokePort j a) (V.spokePort j b) (C.shiftedPort j c t) (C.shiftedPort j d t)+
        segmentCrossingSign (V.spokePort j a) (V.spokePort j b) (C.shiftedPort j c (-t)) (C.shiftedPort j d (-t)))/2 =
      chordEndpointPairing (C.node j a) (C.node j b) (C.node j c) (C.node j d) := by
  classical
  obtain ⟨δ,hδ,hh⟩ := physical_spoke_average_in_similarity (D.vertex j) (C.frame j) (C.frame_ne_zero j)
    (C.node j) (V.spokeScale j) (C.node_injective j) (V.spokeScale_ne_zero j)
  refine ⟨δ,hδ,?_⟩
  intro t ht hsmall a b c d hab hcd
  simpa only [C.point_eq,shiftedPort] using hh t ht hsmall a b c d hab hcd

end TruncatedSpokeCoordinates
end Zarankiewicz

end

end OAI
