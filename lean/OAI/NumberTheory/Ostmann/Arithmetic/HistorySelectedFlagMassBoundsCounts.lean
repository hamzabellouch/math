import OAI.NumberTheory.Ostmann.Arithmetic.CompensationEqualityPatternsHistory
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationNormalizationBudgetCounts
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedFlagMassBoundsBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedFlagMassBounds
open Construction CanonicalOccurrenceTransport

theorem paired_internal_card_le (m k l : ℕ) (hl : l ≤ k) :
    Fintype.card (Internal (Template.initial m k) l ⊕
      Internal (Template.initial m k) l) ≤ occurrenceCap k := by
  rw [HistoryCompensationNormalizationBudget.paired_internal_card m k l hl]
  exact (Nat.mul_le_mul (Nat.mul_le_mul_left 4 hl)
    (Nat.pow_le_pow_right (by norm_num) hl)).trans (Nat.le_max_right _ _)

end Ostmann.Arithmetic.HistorySelectedFlagMassBounds

end

end OAI
