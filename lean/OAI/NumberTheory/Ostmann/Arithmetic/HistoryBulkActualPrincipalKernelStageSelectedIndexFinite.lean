import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStage

theorem index_sum_eq_four_sum {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (a : α → β → γ → δ → ℂ) :
    (∑i : α×(β×γ),∑p,a i.1 i.2.1 i.2.2 p)=∑i,∑j,∑k,∑p,a i j k p := by
  simp only [Fintype.sum_prod_type]

theorem four_sum_bounds_to_index {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (a b : α → β → γ → δ → ℂ) (r₁ r₂ : ℝ)
    (h : ‖(∑i,∑j,∑k,∑p,a i j k p)-(∑i,∑j,∑k,∑p,b i j k p)‖≤r₁ ∧
      ‖(∑i,∑j,∑k,∑p,a i j k p)-(∑i,∑j,∑k,∑p,b i j k p)‖≤r₂) :
    ‖(∑i : α×(β×γ),∑p,a i.1 i.2.1 i.2.2 p)-
      (∑i : α×(β×γ),∑p,b i.1 i.2.1 i.2.2 p)‖≤r₁ ∧
    ‖(∑i : α×(β×γ),∑p,a i.1 i.2.1 i.2.2 p)-
      (∑i : α×(β×γ),∑p,b i.1 i.2.1 i.2.2 p)‖≤r₂ := by
  simpa only [index_sum_eq_four_sum] using h

end Ostmann.Arithmetic.HistoryBulkActualPrincipalKernelStage

end

end OAI
