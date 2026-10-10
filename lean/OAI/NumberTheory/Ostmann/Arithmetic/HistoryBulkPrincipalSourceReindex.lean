import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalSourceReindexBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalSourceReindexPatterns

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPrincipalSourceReindex
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryGiantOriginalMeanFactorization HistoryPairSourceLaws HistoryBulkUniversalPatternAggregation
open scoped BigOperators
local instance principalReindexInternalDecidable (template : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal template l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E)

def pairedChoiceTest (F : Choices (l:=l) C → Choices (l:=l) C → ℂ)
    (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l)
    (z : PairedInternalSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l) : ℂ :=
  F (assembleHistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k)
      (frequencyBound Bs BD Bz k L) l f (fun i=>z (.inl i)))
    (assembleHistoryChoices C.sources (Template.initial (2*(bulkSize k L/2)) k)
      (frequencyBound Bs BD Bz k L) l g (fun i=>z (.inr i)))

def choicePatternValue (F : Choices (l:=l) C → Choices (l:=l) C → ℂ)
    (f g : FrequencyChoices (frequencyBound Bs BD Bz k L) l)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (b : Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) : ℂ :=
  sourcePatternValue C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
    (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l) (pairedChoiceTest C F f g) p b

theorem choicesPairSum_eq_patternMean
    (F : Choices (l:=l) C → Choices (l:=l) C → ℂ) :
    choicesPairSum C F =
      patternComplexSum C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
        (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
        (fun p b=>∑f : FrequencyChoices (frequencyBound Bs BD Bz k L) l,
          ∑g : FrequencyChoices (frequencyBound Bs BD Bz k L) l,choicePatternValue C F f g p b) := by
  rw [choicesPairSum_eq_frequency_sourceMean]
  simp only [patternComplexSum_sum]
  apply Finset.sum_congr rfl
  intro f _
  apply Finset.sum_congr rfl
  intro g _
  exact source_cmean_eq_patternComplexSum C.sources _ _ (pairedChoiceTest C F f g)

theorem commonRootChoicesSum_eq_patternMean
    (F : AllowedFrequency (frequencyBound Bs BD Bz k L) l →
      Choices (l:=l) C → Choices (l:=l) C → ℂ) :
    (∑v,choicesPairSum C (F v)) =
      patternComplexSum C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
        (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
        (fun p b=>∑v : AllowedFrequency (frequencyBound Bs BD Bz k L) l,
          ∑f : FrequencyChoices (frequencyBound Bs BD Bz k L) l,
          ∑g : FrequencyChoices (frequencyBound Bs BD Bz k L) l,choicePatternValue C (F v) f g p b) := by
  simp only [choicesPairSum_eq_patternMean,patternComplexSum_sum]

end Ostmann.Arithmetic.HistoryBulkPrincipalSourceReindex

end

end OAI
