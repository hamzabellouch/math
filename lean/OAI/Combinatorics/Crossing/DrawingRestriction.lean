import OAI.Combinatorics.Crossing.RowCrossingCount
import Mathlib.Order.Fin.Basic

namespace OAI

noncomputable section
namespace Zarankiewicz
variable {m n k : ℕ}

def restrictEdge (f : Fin k ↪ Fin n) : BipartiteEdge m k ↪ BipartiteEdge m n :=
  Function.Embedding.prodMap (Function.Embedding.refl (Fin m)) f

def restrictContinuousDrawing (D : ContinuousDrawing m n) (f : Fin k ↪ Fin n) :
    ContinuousDrawing m k where
  vertex := D.vertex ∘ Sum.map id f
  vertex_injective := D.vertex_injective.comp (Sum.map_injective.mpr ⟨Function.injective_id, f.injective⟩)
  edge e := D.edge (restrictEdge f e)
  edge_injective e := D.edge_injective (restrictEdge f e)
  interior_avoids_vertices e t ht v := D.interior_avoids_vertices (restrictEdge f e) t ht (Sum.map id f v)

theorem restrict_edgeInterior (D : ContinuousDrawing m n) (f : Fin k ↪ Fin n)
    (e : BipartiteEdge m k) :
    edgeInterior (restrictContinuousDrawing D f) e = edgeInterior D (restrictEdge f e) := rfl

theorem restrict_crossingPoints_subset (D : ContinuousDrawing m n) (f : Fin k ↪ Fin n) :
    crossingPoints (restrictContinuousDrawing D f) ⊆ crossingPoints D := by
  rintro x ⟨e,g,heg,he,hg⟩
  exact ⟨restrictEdge f e, restrictEdge f g, (restrictEdge f).injective.ne heg, he, hg⟩

def restrictDrawing (D : AdmissibleDrawing m n) (f : Fin k ↪ Fin n) : AdmissibleDrawing m k where
  toContinuousDrawing := restrictContinuousDrawing D.toContinuousDrawing f
  crossings_finite := D.crossings_finite.subset (restrict_crossingPoints_subset D.toContinuousDrawing f)
  crossings_proper e g heg x he hg :=
    D.crossings_proper (restrictEdge f e) (restrictEdge f g) ((restrictEdge f).injective.ne heg) x he hg
  no_triples e g h heg heh hgh :=
    D.no_triples (restrictEdge f e) (restrictEdge f g) (restrictEdge f h)
      ((restrictEdge f).injective.ne heg) ((restrictEdge f).injective.ne heh) ((restrictEdge f).injective.ne hgh)

theorem crossingCount_restrict_le (D : AdmissibleDrawing m n) (f : Fin k ↪ Fin n) :
    crossingCount (restrictDrawing D f) ≤ crossingCount D := by
  apply Finset.card_le_card
  intro x hx
  have hx' : x ∈ crossingPoints (restrictDrawing D f).toContinuousDrawing := by simpa using hx
  have hh := restrict_crossingPoints_subset D.toContinuousDrawing f hx'
  simpa using hh

theorem restrict_noAdjacentCrossings (D : AdmissibleDrawing m n) (hD : NoAdjacentCrossings D)
    (f : Fin k ↪ Fin n) : NoAdjacentCrossings (restrictDrawing D f) := by
  intro e g heg hadj
  apply hD (restrictEdge f e) (restrictEdge f g) ((restrictEdge f).injective.ne heg)
  rcases hadj with hl | hr
  · exact Or.inl hl
  · exact Or.inr (congrArg f hr)

end Zarankiewicz

end

end OAI
