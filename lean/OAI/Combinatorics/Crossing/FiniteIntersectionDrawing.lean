import OAI.Combinatorics.Crossing.DrawingDefinition
import Mathlib.Data.Set.Card

namespace OAI

noncomputable section
namespace Zarankiewicz

structure FiniteIntersectionDrawing (m n : ℕ) extends ContinuousDrawing m n where
  crossings_finite : (crossingPoints toContinuousDrawing).Finite
  no_triples : ∀ e f g, e ≠ f → e ≠ g → f ≠ g →
    edgeInterior toContinuousDrawing e ∩ edgeInterior toContinuousDrawing f ∩
      edgeInterior toContinuousDrawing g = ∅

abbrev AdmissibleDrawing.toFiniteIntersectionDrawing {m n : ℕ} (D : AdmissibleDrawing m n) :
    FiniteIntersectionDrawing m n where
  toContinuousDrawing := D.toContinuousDrawing
  crossings_finite := D.crossings_finite
  no_triples := D.no_triples

instance admissibleToFiniteIntersectionDrawing {m n : ℕ} :
    CoeOut (AdmissibleDrawing m n) (FiniteIntersectionDrawing m n) :=
  ⟨AdmissibleDrawing.toFiniteIntersectionDrawing⟩

def finiteCrossingCount {m n : ℕ} (D : FiniteIntersectionDrawing m n) : ℕ :=
  D.crossings_finite.toFinset.card

theorem finiteCrossingCount_of_admissible {m n : ℕ} (D : AdmissibleDrawing m n) :
    finiteCrossingCount (D : FiniteIntersectionDrawing m n)=crossingCount D := rfl

theorem finiteCrossingCount_eq_ncard {m n : ℕ} (D : FiniteIntersectionDrawing m n) :
    finiteCrossingCount D=(crossingPoints D.toContinuousDrawing).ncard :=
  (Set.ncard_eq_toFinset_card _ D.crossings_finite).symm

end Zarankiewicz

end

end OAI
