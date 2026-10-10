import OAI.Combinatorics.Crossing.AffineSubdivisionRefinement
import OAI.Combinatorics.Crossing.PolygonalNormalization

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ}

theorem exists_drawing_subdivision_at (D : AdmissibleDrawing m n)
    (hpoly : ∀ e, HasFiniteAffineCover (D.edge e)) (S : Set Plane) (hS : S.Finite) :
    ∃ P : ∀ e, PolygonalParametrization (D.edge e),
      (∀ e t, D.edge e t ∈ drawingMarks D.toFiniteIntersectionDrawing → t ∈ Set.range (P e).knot) ∧
      (∀ e t, D.edge e t ∈ S → t ∈ Set.range (P e).knot) := by
  classical
  have hfinite (e : BipartiteEdge m n) : ((D.edge e) ⁻¹' (drawingMarks D.toFiniteIntersectionDrawing ∪ S)).Finite :=
    ((drawingMarks_finite D.toFiniteIntersectionDrawing).union hS).preimage (D.edge_injective e).injOn
  have hex (e : BipartiteEdge m n) := (hpoly e).refine (hfinite e).toFinset
  choose P hP using hex
  refine ⟨P,?_,?_⟩
  · intro e t ht
    exact hP e (by simpa using Or.inl ht)
  · intro e t ht
    exact hP e (by simpa using Or.inr ht)

namespace PolygonalExterior
variable {D : AdmissibleDrawing m n} {C : DrawingPassages D.toFiniteIntersectionDrawing}

theorem exists_assembled_port_subdivision (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) :
    ∃ P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e),
      (∀ e t, E.assembledEdge v e t ∈ drawingMarks (E.assembledAdmissible v hvinj hv hdet).toFiniteIntersectionDrawing →
        t ∈ Set.range (P e).knot) ∧
      (∀ e t, E.assembledEdge v e t ∈ Set.range C.portPoint → t ∈ Set.range (P e).knot) :=
  exists_drawing_subdivision_at (E.assembledAdmissible v hvinj hv hdet)
    (E.assembledEdge_hasFiniteAffineCover v) (Set.range C.portPoint) (Set.finite_range _)

end PolygonalExterior
end Zarankiewicz

end

end OAI
