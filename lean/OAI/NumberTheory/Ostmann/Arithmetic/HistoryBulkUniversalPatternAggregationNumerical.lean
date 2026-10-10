import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregationNumericalAmplitude
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedUniversalMainBudget

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregation
open Construction Conclusion HistorySelectedJointIntegralBounds Filter

def baseMain (Bs : ℝ) (k : ℕ) (L : ℝ) (l : ℕ) (outside : List ℕ) : ℝ :=
  (64*2^(2^l*(2*(bulkSize k L/2)))*mainAmplitude Bs k L l)*
    (((3:ℝ)^(2^l))^outside.length)*
    Real.exp (2*(2:ℝ)^l*initialGap Bs k L+(bulkSize k L:ℝ))

theorem baseMain_nonneg (Bs : ℝ) (k : ℕ) (L : ℝ) (l : ℕ) (outside : List ℕ) :
    0 ≤ baseMain Bs k L l outside := by
  unfold baseMain
  have ha := mainAmplitude_pos Bs k L l
  positivity

theorem selected_baseMain_aggregation_eventually (Bs : ℝ) {k : ℕ} (hk : 2 ≤ k) :
    ∀ᶠ L : ℝ in atTop, ∀ l ≤ k, ∀ outside : List ℕ,
      outside.length = 2*(bulkSize k L/2) →
      baseMain Bs k L l outside * Real.exp (2*(2:ℝ)^l*(bulkSize k L:ℝ)) ≤
        Real.exp ((2:ℝ)^l*(initialGap Bs k L+16*(bulkSize k L:ℝ))) := by
  filter_upwards [HistorySelectedUniversalMainBudget.selected_universal_main_budget_expanded Bs hk]
    with L hbudget
  intro l hl outside hout
  simpa only [baseMain, hout, mainAmplitude, ← pow_mul, Nat.cast_pow, Nat.cast_ofNat,
    mul_assoc, mul_comm, mul_left_comm] using hbudget l hl

theorem selected_symbolic_main_aggregation_expanded (Bs : ℝ) {k : ℕ} (hk : 2 ≤ k) :
    ∀ᶠ L : ℝ in atTop, ∀ l ≤ k, ∀ outside : List ℕ,
      outside.length = 2*(bulkSize k L/2) →
      ((64*2^(2^l*(2*(bulkSize k L/2)))*mainAmplitude Bs k L l)*
        (((3:ℝ)^(2^l))^outside.length)*
        Real.exp (2*(2:ℝ)^l*initialGap Bs k L+1*(bulkSize k L:ℝ))) *
          Real.exp (2*(2:ℝ)^l*(bulkSize k L:ℝ)) ≤
        Real.exp ((2:ℝ)^l*(initialGap Bs k L+16*(bulkSize k L:ℝ))) := by
  simpa only [baseMain, one_mul] using selected_baseMain_aggregation_eventually Bs hk

end Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregation

end

end OAI
