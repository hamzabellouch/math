import OAI.NumberTheory.Ostmann.Arithmetic.CompensationEqualityPatternsLaws
import OAI.NumberTheory.Ostmann.Arithmetic.CompensationEqualityPatternsTests
import OAI.NumberTheory.Ostmann.Construction.CanonicalHistoryProductChoicesPair

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.CompensationEqualityPatterns
open Construction Construction.CanonicalOccurrenceTransport
open scoped BigOperators
attribute [local instance] Classical.propDecidable

local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) :=
  Classical.decEq _

def historyOrigin (seed : List SourceSlot) (l : ℕ) : Internal seed l → ℕ :=
  fun i => (internalSource seed i).origin

def pairedHistoryType (seed : List SourceSlot) (l : ℕ) :
    Internal seed l ⊕ Internal seed l → ℕ :=
  Sum.elim (internalLevel seed) (internalLevel seed)

theorem sum_history_eq_patterns (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ) (F : HistoryChoices sources seed V l → ℂ) :
    (∑ c : HistoryChoices sources seed V l,
      (choicesMass sources seed V l c : ℂ) * F c) =
      ∑ f : FrequencyChoices V l,
        ∑ p : Pattern (internalLevel seed : Internal seed l → ℕ),
          ∑ b : BlockDraw p (CommonSample sources (historyOrigin seed l)),
            (∏ q : Block p,
              blockWeight p (sourceWeight sources (historyOrigin seed l)) q (b.val q)) •
              extendSourceTest sources (historyOrigin seed l)
                (fun x => F (assembleHistoryChoices sources seed V l f x)) (expand p b) := by
  rw [sum_choicesMass_eq_source_prior]
  apply Finset.sum_congr rfl
  intro f _
  exact source_cmean_arbitrary_eq_patterns sources (historyOrigin seed l)
    (internalLevel seed) (fun x => F (assembleHistoryChoices sources seed V l f x))

theorem sum_pair_history_eq_patterns (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (l : ℕ)
    (F : HistoryChoices sources seed V l → HistoryChoices sources seed V l → ℂ) :
    (∑ c : HistoryChoices sources seed V l, ∑ d : HistoryChoices sources seed V l,
      (choicesMass sources seed V l c : ℂ) *
        (choicesMass sources seed V l d : ℂ) * F c d) =
      ∑ f : FrequencyChoices V l, ∑ g : FrequencyChoices V l,
        ∑ p : Pattern (pairedHistoryType seed l),
          ∑ b : BlockDraw p (CommonSample sources (pairedInternalOrigin seed l)),
            (∏ q : Block p,
              blockWeight p (sourceWeight sources (pairedInternalOrigin seed l)) q (b.val q)) •
              extendSourceTest sources (pairedInternalOrigin seed l)
                (fun z => F
                  (assembleHistoryChoices sources seed V l f (fun i => z (.inl i)))
                  (assembleHistoryChoices sources seed V l g (fun i => z (.inr i))))
                (expand p b) := by
  rw [sum_pair_choicesMass_eq_source_prior]
  apply Finset.sum_congr rfl
  intro f _
  apply Finset.sum_congr rfl
  intro g _
  exact source_cmean_arbitrary_eq_patterns sources (pairedInternalOrigin seed l)
    (pairedHistoryType seed l) (fun z => F
      (assembleHistoryChoices sources seed V l f (fun i => z (.inl i)))
      (assembleHistoryChoices sources seed V l g (fun i => z (.inr i))))

theorem card_pair_history_patterns_le (seed : List SourceSlot) (l : ℕ) :
    Fintype.card (Pattern (pairedHistoryType seed l)) ≤
      2 ^ ((2 * Fintype.card (Internal seed l)) *
        (2 * Fintype.card (Internal seed l))) := by
  simpa only [Fintype.card_sum, two_mul] using card_pattern_le (pairedHistoryType seed l)

theorem pair_history_product_by_multiplicity (sources : SourceFamily)
    (seed : List SourceSlot) (l : ℕ) (p : Pattern (pairedHistoryType seed l))
    (b : BlockDraw p (CommonSample sources (pairedInternalOrigin seed l))) :
    (∏ i : Internal seed l ⊕ Internal seed l, ((expand p b i).val : ℝ)) =
      ∏ q : Block p, ((b.val q).val : ℝ) ^ multiplicity p q :=
  source_product_by_multiplicity sources (pairedInternalOrigin seed l)
    (pairedHistoryType seed l) p b

end Ostmann.Arithmetic.CompensationEqualityPatterns

end

end OAI
