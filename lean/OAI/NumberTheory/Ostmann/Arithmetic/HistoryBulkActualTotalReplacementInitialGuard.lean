import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementBounds

namespace OAI

open Erdos970

namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

theorem same_guard_congr {P : Prop} [Decidable P] (f g : P → ℂ)
    (h : ∀ hp, f hp = g hp) :
    (if hp : P then f hp else 0) = (if hp : P then g hp else 0) := by
  split_ifs with hp
  · exact h hp
  · rfl

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end OAI
