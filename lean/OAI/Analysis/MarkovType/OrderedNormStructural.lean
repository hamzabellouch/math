import OAI.Analysis.MarkovType.OrderedNormConstruction
import OAI.Analysis.MarkovType.JamesEnflo

namespace OAI

namespace MarkovSuperreflexivity

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem orderedNorm_of_not_hasEquivalentUCNorm
    (hnot : ¬ HasEquivalentUCNorm X) :
    ∃ N : OrderedNorm, CoordinatesRepresentable X N := by
  obtain ⟨θ, hθ, s, hrep, hNR⟩ :=
    exists_nonreflexive_finitelyRepresentable_of_not_hasEquivalentUCNorm hnot
  exact exists_orderedNorm_of_nonreflexive_finitelyRepresentable hNR hrep

end MarkovSuperreflexivity

end OAI
