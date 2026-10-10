import OAI.Combinatorics.Crossing.SpokePieceIsolation
import OAI.Combinatorics.Crossing.SpokeEndpointSeparation

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem det2_segmentPoint_sub (d p a b : Plane) (t : ℝ) :
    det2 d (segmentPoint a b t-p)=(1-t)*det2 d (a-p)+t*det2 d (b-p) := by
  dsimp [det2,segmentPoint]
  ring

theorem segment_line_level_zero (a b p : Plane) (hp : p=a ∨ p=b) (t : ℝ) :
    det2 (b-a) (segmentPoint a b t-p)=0 := by
  rcases hp with rfl | rfl <;> dsimp [det2,segmentPoint] <;> ring

namespace VertexTruncation
variable {m n : ℕ} {D : ContinuousDrawing m n} (V : VertexTruncation D)

theorem spokePort_is_piece_endpoint (j : BipartiteVertex m n) (e : IncidentEdges j) :
    V.spokePort j e=V.vertices e.val (V.spokeIndex j e) ∨
      V.spokePort j e=V.vertices e.val (V.spokeIndex j e+1) := by
  unfold spokePort drawingSpokePort spokeIndex
  split_ifs
  · exact Or.inl (V.vertices_first e.val).symm
  · right
    have hp := V.pieces_pos e.val
    rw [show V.pieces e.val-1+1=V.pieces e.val by omega]
    exact (V.vertices_last e.val).symm

end VertexTruncation
namespace TruncatedSpokeCoordinates
variable {m n : ℕ} {D : ContinuousDrawing m n} {V : VertexTruncation D}
  (C : TruncatedSpokeCoordinates V)

theorem continuous_tangentPort (j : BipartiteVertex m n) (e : IncidentEdges j) :
    Continuous (C.tangentPort j e) := by
  change Continuous (fun ε : ℝ => V.spokePort j e+ε • normalShift (V.spokeDirection j e))
  fun_prop

theorem tangentPort_zero (j : BipartiteVertex m n) (e : IncidentEdges j) :
    C.tangentPort j e 0=V.spokePort j e := by simp [tangentPort]

theorem tangentPort_level (j : BipartiteVertex m n) (e : IncidentEdges j) (ε : ℝ) :
    det2 (V.spokeDirection j e) (C.tangentPort j e ε-V.spokePort j e)=ε := by
  simp only [tangentPort,add_sub_cancel_left,det2_smul_right,
    det2_normalShift _ (V.spokeDirection_ne_zero j e),mul_one]

theorem connector_level (j : BipartiteVertex m n) (e : IncidentEdges j) (ε t : ℝ) :
    det2 (V.spokeDirection j e)
      (segmentPoint (C.shiftedPort j e ε) (C.tangentPort j e ε) t-V.spokePort j e)=ε := by
  rw [det2_segmentPoint_sub,C.shiftedPort_level,C.tangentPort_level]
  ring

theorem connector_avoids_incident_piece (j : BipartiteVertex m n) (e : IncidentEdges j)
    (ε : ℝ) (hε : ε ≠ 0) :
    ¬ ClosedSegmentsMeet (V.vertices e.val (V.spokeIndex j e))
      (V.vertices e.val (V.spokeIndex j e+1)) (C.shiftedPort j e ε) (C.tangentPort j e ε) := by
  rintro ⟨s,hs,t,ht,he⟩
  have hzero := segment_line_level_zero (V.vertices e.val (V.spokeIndex j e))
    (V.vertices e.val (V.spokeIndex j e+1)) (V.spokePort j e) (V.spokePort_is_piece_endpoint j e) s
  change det2 (V.spokeDirection j e)
    (segmentPoint (V.vertices e.val (V.spokeIndex j e)) (V.vertices e.val (V.spokeIndex j e+1)) s-V.spokePort j e)=0 at hzero
  rw [he,C.connector_level] at hzero
  exact hε hzero

end TruncatedSpokeCoordinates
end Zarankiewicz

end

end OAI
