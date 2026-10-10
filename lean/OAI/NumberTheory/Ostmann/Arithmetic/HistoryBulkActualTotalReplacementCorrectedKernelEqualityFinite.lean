import Mathlib

namespace OAI

namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

theorem norm_sub_bounds_of_eq {a b c d : ℂ} {r₁ r₂ : ℝ}
    (ha : a=c) (hb : b=d) (h : ‖c-d‖≤r₁ ∧ ‖c-d‖≤r₂) :
    ‖a-b‖≤r₁ ∧ ‖a-b‖≤r₂ := by
  simpa only [ha,hb] using h

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end OAI
