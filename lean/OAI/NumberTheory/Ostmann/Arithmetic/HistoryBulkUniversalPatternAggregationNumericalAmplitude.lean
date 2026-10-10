import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedJointIntegralBoundsNorm

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregationNumerical
open Construction Conclusion HistoryProductWindows HistorySelectedJointIntegralBounds

theorem mainAmplitude_eq_expanded (Bs : ℝ) (k : ℕ) (L : ℝ) (l : ℕ) :
    mainAmplitude Bs k L l =
      Real.exp ((nominalInheritedWidth k l+2)+nominalRemovedWidth k l) *
        Real.exp (-((2^l : ℕ) : ℝ)*initialGap Bs k L+
          sourceXiConstant l k (2+2*(k : ℝ))) := rfl

theorem mainAmplitude_le_expanded (Bs : ℝ) (k : ℕ) (L : ℝ) (l : ℕ) :
    mainAmplitude Bs k L l ≤
      Real.exp ((nominalInheritedWidth k l+2)+nominalRemovedWidth k l) *
        Real.exp (-((2^l : ℕ) : ℝ)*initialGap Bs k L+
          sourceXiConstant l k (2+2*(k : ℝ))) := le_rfl

end Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregationNumerical

end

end OAI
