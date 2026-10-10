import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairBulkCoordinatesMatching
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsSupportTransport

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairSourceLaws
open Construction HistoryOccurrenceVariables HistoryPairPattern HistoryPairRows
open HistoryPairRepresentatives HistoryPairRepresentativeVariables HistoryPairKernelReplacement
open HistoryPairBulkCoordinates
variable {l : ℕ}

theorem smallSourceSamples_of_both_roots_occurrences (sources : SourceFamily)
    (h k : History l) (y : PairKey h k → ℤ)
    (hl : ∀ i : Fin h.root.small.length,
      PositiveSourceValue (sources (h.root.small.get i).origin) (y (rootKey h k i)))
    (hr : ∀ i : Fin k.root.small.length,
      PositiveSourceValue (sources (k.root.small.get i).origin) (y (rightMap h k (.inr (.inl i)))))
    (hi : ∀ i : Occurrences h k,
      PositiveSourceValue (sources (slot h k i).origin)
        (y (representativeMap h k (HistoryPairRepresentatives.label h k i)))) :
    SmallSourceSamples sources h k y := by
  constructor
  · intro i
    rcases i with i | i
    · exact (hl i).sourceMass
    · exact (hi (.inl i)).sourceMass
  · intro i
    rcases i with i | i
    · exact (hr i).sourceMass
    · exact (hi (.inr i)).sourceMass

theorem smallSourceSamples_of_matching_roots_occurrences (sources : SourceFamily)
    (h k : History l) (e : RootMatching h k) (y : PairKey h k → ℤ)
    (hl : ∀ i : Fin h.root.small.length,
      PositiveSourceValue (sources (h.root.small.get i).origin) (y (rootKey h k i)))
    (hr : ∀ i : Fin k.root.small.length,
      PositiveSourceValue (sources (k.root.small.get i).origin) (y (rootKey h k (e.positions i))))
    (hi : ∀ i : Occurrences h k,
      PositiveSourceValue (sources (slot h k i).origin)
        (y (representativeMap h k (HistoryPairRepresentatives.label h k i)))) :
    SmallSourceSamples sources h k y := by
  apply smallSourceSamples_of_both_roots_occurrences sources h k y hl _ hi
  intro i
  rw [e.key_eq]
  exact hr i

end Ostmann.Arithmetic.HistoryPairSourceLaws

end

end OAI
