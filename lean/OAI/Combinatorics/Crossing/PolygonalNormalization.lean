import OAI.Combinatorics.Crossing.AssembledAdmissibleDrawing
import OAI.Combinatorics.Crossing.FiniteAffineCover

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem alternatingPath_hasFiniteAffineCover (a b : ℕ → Plane) (p : ∀ i, Path (a i) (b i))
    (q : ∀ i, Path (b i) (a (i+1))) (hp : ∀ i, HasFiniteAffineCover (p i))
    (hq : ∀ i, HasFiniteAffineCover (q i)) :
    (k : ℕ) → HasFiniteAffineCover (alternatingPath a b p q k)
  | 0 => hp 0
  | k+1 => ((alternatingPath_hasFiniteAffineCover a b p q hp hq k).trans (hq k)).trans (hp (k+1))

namespace PolygonalExterior
variable {m n : ℕ} {D : FiniteIntersectionDrawing m n} {C : DrawingPassages D}

theorem middlePath_hasFiniteAffineCover (E : PolygonalExterior C) (e : BipartiteEdge m n) :
    HasFiniteAffineCover (E.middlePath e) :=
  alternatingPath_hasFiniteAffineCover _ _ _ _ (fun i => (E.chain (C.orderedArc e i)).hasFiniteAffineCover)
    (fun _ => hasFiniteAffineCover_segment _ _) _

theorem assembledEdge_hasFiniteAffineCover (E : PolygonalExterior C)
    (v : BipartiteVertex m n → Plane) (e : BipartiteEdge m n) :
    HasFiniteAffineCover (E.assembledEdge v e) := by
  apply HasFiniteAffineCover.trans
  · apply HasFiniteAffineCover.trans (hasFiniteAffineCover_segment _ _)
    exact E.middlePath_hasFiniteAffineCover e
  · simp only [endSpoke,Path.segment_symm]
    exact hasFiniteAffineCover_segment _ _

end PolygonalExterior

theorem finite_intersection_normalization {m n : ℕ} (D : FiniteIntersectionDrawing m n) :
    ∃ D' : AdmissibleDrawing m n,
      (∀ e, HasFiniteAffineCover (D'.edge e)) ∧ crossingCount D' ≤ finiteCrossingCount D := by
  obtain ⟨C⟩ := nonempty_drawingPassages D
  obtain ⟨E⟩ := nonempty_polygonalExterior C
  obtain ⟨v,hvinj,hv,hne,hdet⟩ := C.exists_drawing_vertex_placement
  exact ⟨E.assembledAdmissible v hvinj hv hdet,E.assembledEdge_hasFiniteAffineCover v,
    E.assembled_crossingCount_le v hvinj hv hdet⟩

theorem polygonal_normalization {m n : ℕ} (D : AdmissibleDrawing m n) :
    ∃ D' : AdmissibleDrawing m n,
      (∀ e, HasFiniteAffineCover (D'.edge e)) ∧ crossingCount D' ≤ crossingCount D := by
  obtain ⟨C⟩ := nonempty_drawingPassages D.toFiniteIntersectionDrawing
  obtain ⟨E⟩ := nonempty_polygonalExterior C
  obtain ⟨v,hvinj,hv,hne,hdet⟩ := C.exists_drawing_vertex_placement
  exact ⟨E.assembledAdmissible v hvinj hv hdet,E.assembledEdge_hasFiniteAffineCover v,
    E.assembled_crossingCount_le v hvinj hv hdet⟩

end Zarankiewicz

end

end OAI
