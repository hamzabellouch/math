import OAI.Combinatorics.Crossing.SegmentAugmentation
import OAI.Combinatorics.Crossing.ReconnectionChords
import OAI.Combinatorics.Crossing.SubdivisionPointEndpoints
import OAI.Combinatorics.Crossing.ExteriorSegmentGraph

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n : ℕ} {D D' : AdmissibleDrawing m n}

def crossingSurgeryGraph (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q : C.InnerIndex) : SimpleGraph Plane :=
  segmentAugmentedGraph (exteriorSegmentGraph (drawingSubdivisionGraph P) (C.crossingDisk p))
    (C.reconnectionStart p q) (C.reconnectionEnd p q) (C.reconnection_endpoints_ne p q)

theorem crossingSurgeryGraph_embedding (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e))
    (hmark : ∀ e t, D'.edge e t ∈ drawingMarks D'.toFiniteIntersectionDrawing → t ∈ Set.range (P e).knot)
    (hport : ∀ e t, D'.edge e t ∈ Set.range C.portPoint → t ∈ Set.range (P e).knot)
    (p q : C.InnerIndex) (hm : C.innerMark p=C.innerMark q)
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q))) :
    StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id := by
  have hemb := drawingSubdivisionGraph_embedding P hmark
  have houtEmb : StraightEdgeEmbedding
      (exteriorSegmentGraph (drawingSubdivisionGraph P) (C.crossingDisk p)) id := by
    refine ⟨hemb.1,?_⟩
    intro a b c d hab hcd x hx hy
    exact hemb.2 a b c d hab.1 hcd.1 x hx hy
  apply segmentAugmentedGraph_embedding _ _ _ _ houtEmb (C.crossingDisk p)
  · intro x y hxy
    exact hxy.2
  · exact C.reconnection_open_in_disk p q hm
  · exact C.reconnection_chords_disjoint p q hcross
  · intro i x y hxy
    constructor
    · apply drawingSubdivisionGraph_point_endpoint P _ ?_ x y hxy.1
      intro e t ht
      apply hport e t
      cases i
      · exact ⟨C.incomingPort q,ht.symm⟩
      · exact ⟨C.incomingPort p,ht.symm⟩
    · apply drawingSubdivisionGraph_point_endpoint P _ ?_ x y hxy.1
      intro e t ht
      apply hport e t
      cases i
      · exact ⟨C.outgoingPort p,ht.symm⟩
      · exact ⟨C.outgoingPort q,ht.symm⟩

theorem exterior_le_crossingSurgeryGraph (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q : C.InnerIndex) :
    exteriorSegmentGraph (drawingSubdivisionGraph P) (C.crossingDisk p) ≤ crossingSurgeryGraph C P p q :=
  le_segmentAugmentedGraph _ _ _ _

theorem crossingSurgeryGraph_reconnection_adj (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q : C.InnerIndex) (i : Bool) :
    (crossingSurgeryGraph C P p q).Adj (C.reconnectionStart p q i) (C.reconnectionEnd p q i) :=
  segmentAugmentedGraph_added_adj _ _ _ _ i

end Zarankiewicz

end

end OAI
