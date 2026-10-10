import OAI.Combinatorics.Crossing.PolygonalChainComposition

namespace OAI

noncomputable section
namespace Zarankiewicz.PolygonalChain
variable {O T : Set Plane} {a b c d e : Plane}

def Transverse (P : PolygonalChain O a b) (Q : PolygonalChain T d e) : Prop :=
  ∀ i : Fin P.pieces, ∀ j : Fin Q.pieces,
    SegmentPairTransverse (P.vertices i.val) (P.vertices (i.val+1))
      (Q.vertices j.val) (Q.vertices (j.val+1))

theorem transverse_swap (P : PolygonalChain O a b) (Q : PolygonalChain T d e)
    (h : P.Transverse Q) : Q.Transverse P :=
  fun j i => segmentPairTransverse_swap _ _ _ _ (h i j)

theorem transverse_join_left (P : PolygonalChain O a b) (Q : PolygonalChain O b c)
    (R : PolygonalChain T d e) (hP : P.Transverse R) (hQ : Q.Transverse R) :
    (P.join Q).Transverse R := by
  intro i j
  change SegmentPairTransverse (joinedSequence P.vertices Q.vertices P.pieces i.val)
    (joinedSequence P.vertices Q.vertices P.pieces (i.val+1)) _ _
  have hi : i.val<P.pieces+Q.pieces := i.isLt
  by_cases hip : i.val<P.pieces
  · rw [joinedSequence_left _ _ _ (P.last.trans Q.first.symm) i.val hip.le,
      joinedSequence_left _ _ _ (P.last.trans Q.first.symm) (i.val+1) (by omega)]
    exact hP ⟨i.val,hip⟩ j
  · have he : i.val=P.pieces+(i.val-P.pieces) := by omega
    have he' : i.val+1=P.pieces+(i.val-P.pieces+1) := by omega
    have h₀ : joinedSequence P.vertices Q.vertices P.pieces i.val=Q.vertices (i.val-P.pieces) := by
      conv_lhs => rw [he]
      exact joinedSequence_right _ _ _ _
    have h₁ : joinedSequence P.vertices Q.vertices P.pieces (i.val+1)=Q.vertices (i.val-P.pieces+1) := by
      rw [he',joinedSequence_right]
    rw [h₀,h₁]
    exact hQ ⟨i.val-P.pieces,by omega⟩ j

theorem transverse_join_right (P : PolygonalChain O a b) (Q : PolygonalChain O b c)
    (R : PolygonalChain T d e) (hP : R.Transverse P) (hQ : R.Transverse Q) :
    R.Transverse (P.join Q) :=
  (P.join Q).transverse_swap R (P.transverse_join_left Q R (R.transverse_swap P hP) (R.transverse_swap Q hQ))

theorem closed_intersection_zero (P : PolygonalChain O a a) (Q : PolygonalChain T d d)
    (h : P.Transverse Q) : polygonIntersection P.vertices Q.vertices P.pieces Q.pieces=0 :=
  closed_polygon_intersection_zero _ _ _ _ (P.last.trans P.first.symm) (Q.last.trans Q.first.symm) h

end Zarankiewicz.PolygonalChain

end

end OAI
