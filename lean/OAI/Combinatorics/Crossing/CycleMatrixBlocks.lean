import OAI.Combinatorics.Crossing.AdditiveBlockRelation
import OAI.Combinatorics.Crossing.DetectorCrossingBound

namespace OAI

noncomputable section
namespace Zarankiewicz.TruncatedSpokeCoordinates
variable {m n : ℕ} {D : AdmissibleDrawing m n} {V : VertexTruncation D.toContinuousDrawing}
  (C : TruncatedSpokeCoordinates V)

def leftHalfOrder (i : Fin m) : Matrix (Fin n) (Fin n) ℝ := fun p q =>
  orderSign (C.node (Sum.inl i) (V.leftIncident (i,p))) (C.node (Sum.inl i) (V.leftIncident (i,q)))/2

def rightHalfOrder (p : Fin n) : Matrix (Fin m) (Fin m) ℝ := fun i k =>
  orderSign (C.node (Sum.inr p) (V.rightIncident (i,p))) (C.node (Sum.inr p) (V.rightIncident (k,p)))/2

theorem flagPairing_left_block (i k : Fin m) (p q : Fin n) :
    C.flagPairing (dartSourceFlag (forwardBipartiteDart (i,p)))
      (dartSourceFlag (forwardBipartiteDart (k,q)))=if i=k then C.leftHalfOrder i p q else 0 := by
  by_cases h : i=k
  · subst k
    change (if h : (Sum.inl i : BipartiteVertex m n)=Sum.inl i then
      orderSign (C.node (Sum.inl i) (V.leftIncident (i,p)))
        (C.node (Sum.inl i) (incidentCast h (V.leftIncident (i,q))))/2 else 0)=_
    rw [dite_eq_left rfl,incidentCast_refl,ite_eq_left rfl]
    rfl
  · have hn : (Sum.inl k : BipartiteVertex m n) ≠ Sum.inl i := fun he => h (Sum.inl.inj he).symm
    simp only [flagPairing,dartSourceFlag,forwardBipartiteDart,ite_eq_right h]
    exact dite_eq_right hn

theorem flagPairing_right_block (i k : Fin m) (p q : Fin n) :
    C.flagPairing (dartTargetFlag (forwardBipartiteDart (i,p)))
      (dartTargetFlag (forwardBipartiteDart (k,q)))=if p=q then C.rightHalfOrder p i k else 0 := by
  by_cases h : p=q
  · subst q
    change (if h : (Sum.inr p : BipartiteVertex m n)=Sum.inr p then
      orderSign (C.node (Sum.inr p) (V.rightIncident (i,p)))
        (C.node (Sum.inr p) (incidentCast h (V.rightIncident (k,p))))/2 else 0)=_
    rw [dite_eq_left rfl,incidentCast_refl,ite_eq_left rfl]
    rfl
  · have hn : (Sum.inr q : BipartiteVertex m n) ≠ Sum.inr p := fun he => h (Sum.inr.inj he).symm
    simp only [flagPairing,dartTargetFlag,forwardBipartiteDart,ite_eq_right h]
    exact dite_eq_right hn

theorem cycleIntersectionMatrix_entry (i k : Fin m) (p q : Fin n) :
    C.cycleIntersectionMatrix (i,p) (k,q)=V.signedIntersection (i,p) (k,q)+
      (if i=k then C.leftHalfOrder i p q else 0)+(if p=q then C.rightHalfOrder p i k else 0) := by
  rw [cycleIntersectionMatrix,edgeEndpointPairing,C.flagPairing_left_block,C.flagPairing_right_block]
  ring

theorem cycleIntersectionMatrix_diagonal_block (hnorm : NoAdjacentCrossings D) (i : Fin m) :
    edgeBlock C.cycleIntersectionMatrix i i=C.leftHalfOrder i := by
  ext p q
  rw [edgeBlock,C.cycleIntersectionMatrix_entry,V.signedIntersection_adjacent_zero hnorm (i,p) (i,q) (Or.inl rfl),ite_eq_left rfl]
  have hz : C.rightHalfOrder p i i=0 := by simp [rightHalfOrder,orderSign]
  rw [hz]
  simp

theorem cycleIntersectionMatrix_offDiagonal_block (i k : Fin m) (hik : i ≠ k) :
    edgeBlock C.cycleIntersectionMatrix i k=V.intersectionBlock i k+
      Matrix.diagonal (fun p => C.rightHalfOrder p i k) := by
  ext p q
  rw [edgeBlock,C.cycleIntersectionMatrix_entry,ite_eq_right hik]
  simp only [Matrix.add_apply,VertexTruncation.intersectionBlock,Matrix.diagonal_apply,add_zero]

end Zarankiewicz.TruncatedSpokeCoordinates

end

end OAI
