import OAI.Analysis.MarkovType.SpreadingConstruction
import OAI.Analysis.MarkovType.SubdivisionOrderedNorm
import OAI.Analysis.MarkovType.CoordinateRepresentability

namespace OAI

namespace MarkovSuperreflexivity

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

theorem exists_orderedNorm_of_nonreflexive_finitelyRepresentable
    (hNR : ¬ CanonicallyReflexive Y) (hYX : FinitelyRepresentable Y X) :
    ∃ N : OrderedNorm, CoordinatesRepresentable X N := by
  obtain ⟨S⟩ := exists_spreadingModel_of_nonreflexive hNR
  obtain ⟨N, hNY⟩ := exists_orderedNorm_of_spreadingModel S
  exact ⟨N, hNY.transfer hYX⟩

end MarkovSuperreflexivity

end OAI
