import OAI.Combinatorics.Crossing.AdjacentSurgeryDrawing
import OAI.Combinatorics.Crossing.PolygonalParametrizationCover

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D D' : AdmissibleDrawing m n}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}

theorem adjacentSurgeryDrawing_hasFiniteAffineCover
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hpq : p ≠ q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (e : BipartiteEdge m n) : HasFiniteAffineCover ((adjacentSurgeryDrawing Kp Kq hm hadj hv hemb).edge e) := by
  classical
  by_cases hep : e=p.1
  · subst e
    rw [adjacentSurgeryDrawing_first]
    exact adjacentSurgeryRouteP_hasFiniteAffineCover Kp Kq hm hadj
  by_cases heq : e=q.1
  · subst e
    rw [adjacentSurgeryDrawing_second Kp Kq hm hpq]
    exact adjacentSurgeryRouteQ_hasFiniteAffineCover Kp Kq hm hadj
  · rw [adjacentSurgeryDrawing_other Kp Kq hm hadj hv hemb e hep heq]
    exact (P e).hasFiniteAffineCover

theorem adjacentSurgeryRoutes_avoid_crossing
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hpq : p ≠ q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    x ∉ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj) ∧
      x ∉ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj) := by
  have ha := reconnected_paths_avoid_crossing Kp Kq hm hpq x hxp hxq
  constructor
  · unfold adjacentSurgeryRouteP
    split
    · exact ha.2
    · exact ha.1
  · unfold adjacentSurgeryRouteQ
    split
    · exact ha.1
    · exact ha.2

theorem adjacentSurgeryDrawing_avoids_crossing
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hpq : p ≠ q) (hadj : p.1.1=q.1.1 ∨ p.1.2=q.1.2)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q))
    (hother : ∀ e, e ≠ p.1 → e ≠ q.1 → x ∉ Set.range (D'.edge e)) :
    ∀ e, x ∉ Set.range ((adjacentSurgeryDrawing Kp Kq hm hadj hv hemb).edge e) := by
  have ha := adjacentSurgeryRoutes_avoid_crossing Kp Kq hm hpq hadj x hxp hxq
  intro e
  classical
  by_cases hep : e=p.1
  · subst e
    rw [adjacentSurgeryDrawing_first]
    exact ha.1
  by_cases heq : e=q.1
  · subst e
    rw [adjacentSurgeryDrawing_second Kp Kq hm hpq]
    exact ha.2
  · rw [adjacentSurgeryDrawing_other Kp Kq hm hadj hv hemb e hep heq]
    exact hother e hep heq

end Zarankiewicz

end

end OAI
