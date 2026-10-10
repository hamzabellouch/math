import OAI.Combinatorics.Crossing.VertexTruncationGeometry
import OAI.Combinatorics.Crossing.SpokeTrackDirections

namespace OAI

noncomputable section
namespace Zarankiewicz.VertexTruncation
variable {m n : ℕ} {D : ContinuousDrawing m n} (V : VertexTruncation D)

def spokePort (j : BipartiteVertex m n) (e : IncidentEdges j) : Plane :=
  drawingSpokePort D V.chain V.radius j e

def spokeIndex (j : BipartiteVertex m n) (e : IncidentEdges j) : ℕ :=
  if j=Sum.inl e.val.1 then 0 else V.pieces e.val-1

def spokeDirection (j : BipartiteVertex m n) (e : IncidentEdges j) : Plane :=
  trackDirection (V.vertices e.val) (V.spokeIndex j e)

theorem spokeIndex_lt (j : BipartiteVertex m n) (e : IncidentEdges j) :
    V.spokeIndex j e < V.pieces e.val := by
  have hp := V.pieces_pos e.val
  unfold spokeIndex
  split_ifs <;> omega

theorem spokeDirection_ne_zero (j : BipartiteVertex m n) (e : IncidentEdges j) :
    V.spokeDirection j e ≠ 0 := V.direction_ne_zero e.val _ (V.spokeIndex_lt j e)

theorem spokeDirection_eq_scale (j : BipartiteVertex m n) (e : IncidentEdges j) :
    V.spokeDirection j e =
      (V.chain e.val).truncatedScale V.radius (V.spokeIndex j e) •
        drawingSpokeDirection D V.chain j e := by
  change trackDirection ((V.chain e.val).truncatedVertices V.radius) (V.spokeIndex j e)=_
  rw [(V.chain e.val).truncated_direction V.radius _ (V.spokeIndex_lt j e)]
  congr 1
  unfold spokeIndex drawingSpokeDirection
  split_ifs <;> rfl

theorem spokePort_circle (j : BipartiteVertex m n) (e : IncidentEdges j) :
    squaredLength (V.spokePort j e-D.vertex j)=V.radius^2 :=
  drawingSpokePort_circle D V.chain V.minimal V.radius j e

theorem spokePort_ne_center (j : BipartiteVertex m n) (e : IncidentEdges j) :
    V.spokePort j e-D.vertex j ≠ 0 := by
  intro h
  have hc := V.spokePort_circle j e
  rw [h] at hc
  have hz : squaredLength (0 : Plane)=0 := by simp [squaredLength]
  rw [hz] at hc
  nlinarith [V.radius_pos]

theorem spokeDirection_parallel (j : BipartiteVertex m n) (e : IncidentEdges j) :
    det2 (V.spokeDirection j e) (V.spokePort j e-D.vertex j)=0 := by
  rw [V.spokeDirection_eq_scale,det2_smul_left]
  have hp := drawingSpokeDirection_port_parallel D V.chain V.radius j e (V.pieces_pos e.val)
  change det2 (drawingSpokeDirection D V.chain j e) (V.spokePort j e-D.vertex j)=0 at hp
  rw [hp,mul_zero]

def spokeScale (j : BipartiteVertex m n) (e : IncidentEdges j) : ℝ :=
  circleTrackScale (V.spokeDirection j e) (V.spokePort j e-D.vertex j)

theorem spokeScale_ne_zero (j : BipartiteVertex m n) (e : IncidentEdges j) :
    V.spokeScale j e ≠ 0 :=
  circleTrackScale_ne_zero _ _ (V.spokeDirection_ne_zero j e)
    (V.spokePort_ne_center j e) (V.spokeDirection_parallel j e)

theorem spokePort_injective {A : AdmissibleDrawing m n}
    (V : VertexTruncation A.toContinuousDrawing) (hnorm : NoAdjacentCrossings A)
    (j : BipartiteVertex m n) : Function.Injective (V.spokePort j) :=
  drawingSpokePort_injective A hnorm V.chain V.minimal V.radius V.radius_pos V.weak_short j

end Zarankiewicz.VertexTruncation

end

end OAI
