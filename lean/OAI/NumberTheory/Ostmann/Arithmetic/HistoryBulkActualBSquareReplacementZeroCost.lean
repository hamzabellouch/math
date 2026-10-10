import OAI.NumberTheory.Ostmann.Conclusion.Scales

namespace OAI

namespace Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement

theorem zero_cost_bounds (L x a b : ℝ)
    (h : Real.exp (0*(L+1)^2)*x≤a ∧ Real.exp (0*(L+1)^2)*x≤b) :
    x≤a ∧ x≤b := by
  simpa only [zero_mul,Real.exp_zero,one_mul] using h

end Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement

end OAI
