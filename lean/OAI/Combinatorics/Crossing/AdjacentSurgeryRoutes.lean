import OAI.Combinatorics.Crossing.ReplaceDrawingEdges
import OAI.Combinatorics.Crossing.ReconnectedPointRemoval

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D D' : AdmissibleDrawing m n}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}

def adjacentSurgeryRouteP (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2) :
    Path (D'.vertex (.inl p.1.1)) (D'.vertex (.inr p.1.2)) := by
  classical
  exact if h : p.1.1=q.1.1 then (reconnectedBackwardPath Kp Kq hm).cast
    (congrArg (fun i => D'.vertex (.inl i)) h) rfl
  else (reconnectedForwardPath Kp Kq hm).cast rfl
    (congrArg (fun j => D'.vertex (.inr j)) (hadj.resolve_left h))

def adjacentSurgeryRouteQ (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2) :
    Path (D'.vertex (.inl q.1.1)) (D'.vertex (.inr q.1.2)) := by
  classical
  exact if h : p.1.1=q.1.1 then (reconnectedForwardPath Kp Kq hm).cast
    (congrArg (fun i => D'.vertex (.inl i)) h.symm) rfl
  else (reconnectedBackwardPath Kp Kq hm).cast rfl
    (congrArg (fun j => D'.vertex (.inr j)) (hadj.resolve_left h).symm)

theorem adjacentSurgeryRouteP_injective (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    Function.Injective (adjacentSurgeryRouteP Kp Kq hm hadj) := by
  unfold adjacentSurgeryRouteP
  split
  · exact reconnectedBackwardPath_injective Kp Kq hm hemb
  · exact reconnectedForwardPath_injective Kp Kq hm hemb

theorem adjacentSurgeryRouteQ_injective (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    Function.Injective (adjacentSurgeryRouteQ Kp Kq hm hadj) := by
  unfold adjacentSurgeryRouteQ
  split
  · exact reconnectedForwardPath_injective Kp Kq hm hemb
  · exact reconnectedBackwardPath_injective Kp Kq hm hemb

theorem adjacentSurgeryRouteP_avoids_vertices
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) (j : BipartiteVertex m n) :
    adjacentSurgeryRouteP Kp Kq hm hadj t ≠ D'.vertex j := by
  unfold adjacentSurgeryRouteP
  split
  · exact reconnectedBackwardPath_interior_avoids_vertices Kp Kq hm hv hemb t ht j
  · exact reconnectedForwardPath_interior_avoids_vertices Kp Kq hm hv hemb t ht j

theorem adjacentSurgeryRouteQ_avoids_vertices
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) (j : BipartiteVertex m n) :
    adjacentSurgeryRouteQ Kp Kq hm hadj t ≠ D'.vertex j := by
  unfold adjacentSurgeryRouteQ
  split
  · exact reconnectedForwardPath_interior_avoids_vertices Kp Kq hm hv hemb t ht j
  · exact reconnectedBackwardPath_interior_avoids_vertices Kp Kq hm hv hemb t ht j

end Zarankiewicz

end

end OAI
