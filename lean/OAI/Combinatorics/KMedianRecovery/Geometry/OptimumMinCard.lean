import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Produce

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [PseudoMetricSpace V]

lemma optimum_min_card (F D : Finset V) (k : ℕ) :
    optimum F D (min k F.card) = optimum F D k := by
  have he : feasibleSets F (min k F.card) = feasibleSets F k := by
    ext S
    simp only [mem_feasibleSets]
    constructor
    · rintro ⟨hSF,hS,hSk⟩
      exact ⟨hSF,hS,hSk.trans (min_le_left _ _)⟩
    · rintro ⟨hSF,hS,hSk⟩
      exact ⟨hSF,hS,le_min hSk (Finset.card_le_card hSF)⟩
  simp only [optimum,he]

end MetricKMedianRecovery.LocalSearch

end OAI
