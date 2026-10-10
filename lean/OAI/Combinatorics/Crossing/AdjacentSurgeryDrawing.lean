import OAI.Combinatorics.Crossing.AdjacentSurgeryRoutes

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D D' : AdmissibleDrawing m n}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}

def adjacentSurgeryDrawing (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) : ContinuousDrawing m n :=
  D'.toContinuousDrawing.replaceTwoEdges p.1 q.1
    (adjacentSurgeryRouteP Kp Kq hm hadj) (adjacentSurgeryRouteQ Kp Kq hm hadj)
    (adjacentSurgeryRouteP_injective Kp Kq hm hadj hemb)
    (adjacentSurgeryRouteQ_injective Kp Kq hm hadj hemb)
    (adjacentSurgeryRouteP_avoids_vertices Kp Kq hm hadj hv hemb)
    (adjacentSurgeryRouteQ_avoids_vertices Kp Kq hm hadj hv hemb)

theorem adjacentSurgeryDrawing_vertex (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb).vertex=D'.vertex := rfl

theorem adjacentSurgeryDrawing_first (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb).edge p.1=adjacentSurgeryRouteP Kp Kq hm hadj :=
  ContinuousDrawing.replaceTwoRoutes_first _ _ _ _ _

theorem adjacentSurgeryDrawing_second (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hpq : p ≠ q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb).edge q.1=adjacentSurgeryRouteQ Kp Kq hm hadj :=
  ContinuousDrawing.replaceTwoRoutes_second _ _ _ (fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hm)) _ _

theorem adjacentSurgeryDrawing_other (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (e : BipartiteEdge m n) (hep : e ≠ p.1) (heq : e ≠ q.1) :
    (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb).edge e=D'.edge e :=
  ContinuousDrawing.replaceTwoRoutes_other _ _ _ _ _ _ hep heq

theorem adjacentSurgeryRouteP_hasFiniteAffineCover
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2) :
    HasFiniteAffineCover (adjacentSurgeryRouteP Kp Kq hm hadj) := by
  unfold adjacentSurgeryRouteP
  split
  · exact (reconnectedBackwardPath_hasFiniteAffineCover Kp Kq hm).cast _ _
  · exact (reconnectedForwardPath_hasFiniteAffineCover Kp Kq hm).cast _ _

theorem adjacentSurgeryRouteQ_hasFiniteAffineCover
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2) :
    HasFiniteAffineCover (adjacentSurgeryRouteQ Kp Kq hm hadj) := by
  unfold adjacentSurgeryRouteQ
  split
  · exact (reconnectedForwardPath_hasFiniteAffineCover Kp Kq hm).cast _ _
  · exact (reconnectedBackwardPath_hasFiniteAffineCover Kp Kq hm).cast _ _

end Zarankiewicz

end

end OAI
