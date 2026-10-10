import OAI.Combinatorics.Crossing.IncidentSpokePorts
import OAI.Combinatorics.Crossing.CircleOffsetLine

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

def drawingSpokeDirection (D : ContinuousDrawing m n)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (j : BipartiteVertex m n) (e : IncidentEdges j) : Plane :=
  if j=Sum.inl e.val.1 then trackDirection (P e.val).vertices 0
    else trackDirection (P e.val).vertices ((P e.val).pieces-1)

theorem drawingSpokeDirection_ne_zero (D : ContinuousDrawing m n)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)), (P e).pieces ≤ Q.pieces)
    (j : BipartiteVertex m n) (e : IncidentEdges j) : drawingSpokeDirection D P j e ≠ 0 := by
  have hp := drawing_chain_pieces_pos D e.val (P e.val)
  unfold drawingSpokeDirection
  split_ifs
  · exact (P e.val).minimum_piece_ne_zero (hmin e.val) 0 hp
  · exact (P e.val).minimum_piece_ne_zero (hmin e.val) ((P e.val).pieces-1) (by omega)

theorem drawingSpokeDirection_port_parallel (D : ContinuousDrawing m n)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (r : ℝ) (j : BipartiteVertex m n) (e : IncidentEdges j)
    (hpos : 0 < (P e.val).pieces) :
    det2 (drawingSpokeDirection D P j e) (drawingSpokePort D P r j e-D.vertex j)=0 := by
  unfold drawingSpokeDirection drawingSpokePort
  split_ifs with h
  · have hc : D.vertex j=(P e.val).vertices 0 := (congrArg D.vertex h).trans (P e.val).first.symm
    rw [hc]
    change det2 ((P e.val).vertices 1-(P e.val).vertices 0)
      (radialPort ((P e.val).vertices 0) ((P e.val).vertices 1) r-(P e.val).vertices 0)=0
    rw [radialPort_sub,det2_smul_right,det2_self,mul_zero]
  · have he := e.property.resolve_left h
    have hc : D.vertex j=(P e.val).vertices (P e.val).pieces :=
      (congrArg D.vertex he).trans (P e.val).last.symm
    rw [hc]
    simp only [trackDirection,PolygonalChain.endPort,
      show (P e.val).pieces-1+1=(P e.val).pieces by omega,radialPort_sub,det2_smul_right]
    have hn : (P e.val).vertices ((P e.val).pieces-1)-(P e.val).vertices (P e.val).pieces =
        -((P e.val).vertices (P e.val).pieces-(P e.val).vertices ((P e.val).pieces-1)) := by abel
    rw [hn,det2_neg_right,det2_self,neg_zero,mul_zero]

theorem drawingSpokeScale_ne_zero (D : ContinuousDrawing m n)
    (P : ∀ e : BipartiteEdge m n, PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)))
    (hmin : ∀ e, ∀ Q : PolygonalChain (Set.range (D.edge e))
      (D.vertex (.inl e.1)) (D.vertex (.inr e.2)), (P e).pieces ≤ Q.pieces)
    (r : ℝ) (hr : 0 < r) (j : BipartiteVertex m n) (e : IncidentEdges j) :
    circleTrackScale (drawingSpokeDirection D P j e) (drawingSpokePort D P r j e-D.vertex j) ≠ 0 := by
  have hw : drawingSpokePort D P r j e-D.vertex j ≠ 0 := by
    intro hh
    have hc := drawingSpokePort_circle D P hmin r j e
    rw [hh] at hc
    have hz : squaredLength (0 : Plane)=0 := by simp [squaredLength]
    rw [hz] at hc
    nlinarith
  exact circleTrackScale_ne_zero _ _ (drawingSpokeDirection_ne_zero D P hmin j e) hw
    (drawingSpokeDirection_port_parallel D P r j e (drawing_chain_pieces_pos D e.val (P e.val)))

end Zarankiewicz

end

end OAI
