import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantCounterpartBoundsSelected

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantCounterpartBounds
open HistoryProductWindows

theorem counterpartWidths_sum (k l : ℕ) :
    (nominalInheritedWidth k l+2)+nominalRemovedWidth k l=
      3+(2:ℝ)^l*(18+10*(k:ℝ)) := by
  unfold nominalInheritedWidth nominalRemovedWidth
  ring

theorem counterpartWidths_nonneg (k l : ℕ) :
    0 ≤ nominalInheritedWidth k l+2 ∧ 0 ≤ nominalRemovedWidth k l := by
  unfold nominalInheritedWidth nominalRemovedWidth
  constructor <;> positivity

end Ostmann.Arithmetic.HistoryGiantCounterpartBounds

end

end OAI
