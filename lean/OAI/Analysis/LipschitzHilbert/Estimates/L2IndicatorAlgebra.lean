import OAI.Analysis.LipschitzHilbert.Estimates.L2Indicator

namespace OAI

/-! Nested measurable cutoffs on L2. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert
variable {X : Type*} [MeasurableSpace X]

theorem l2Indicator_nested (mu : Measure X) (S T : Set X) (hS : MeasurableSet S)
    (hT : MeasurableSet T) (hST : S⊆T) (f : Lp ℂ 2 mu) :
    l2Indicator mu S hS (l2Indicator mu T hT f)=l2Indicator mu S hS f := by
  apply Lp.ext
  filter_upwards [l2Indicator_coe mu S hS (l2Indicator mu T hT f),
    l2Indicator_coe mu T hT f,l2Indicator_coe mu S hS f] with z h1 h2 h3
  rw [h1,h3]
  by_cases hz : z∈S
  · simp only [Set.indicator_of_mem hz,h2,Set.indicator_of_mem (hST hz)]
  · simp only [Set.indicator_of_notMem hz]

theorem l2Indicator_idempotent (mu : Measure X) (S : Set X) (hS : MeasurableSet S)
    (f : Lp ℂ 2 mu) : l2Indicator mu S hS (l2Indicator mu S hS f)=l2Indicator mu S hS f :=
  l2Indicator_nested mu S S hS hS (Subset.rfl) f

theorem l2Indicator_norm_le (mu : Measure X) (S : Set X) (hS : MeasurableSet S)
    (f : Lp ℂ 2 mu) : ‖l2Indicator mu S hS f‖≤‖f‖ := l2IndicatorLM_norm mu S hS f

end LipschitzHilbert

end

end OAI
