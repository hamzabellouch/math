import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedRootErrorBudgetBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedRootErrorBudgetNumerics

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistorySelectedRootErrorBudget
open Construction Conclusion Filter

theorem selected_nested_root_error_eventually (Bs BD Bz H : ℝ) (hH : 0 ≤ H)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ l ≤ k,
    ∀ (α β : Type*) [Fintype α] [Fintype β]
      (μ : FinitePrior α) (ν : α → FinitePrior β)
      (F : α → β → AllowedFrequency (frequencyBound Bs BD Bz k L) l → ℂ),
      (∀ a, μ.mass a ≠ 0 → ∀ b, (ν a).mass b ≠ 0 → ∀ r,
        ‖F a b r‖ ≤ Real.exp (-Real.exp ((21/2000:ℝ)*L))) →
      ‖μ.cmean (fun a => (ν a).cmean (fun b => ∑ r, F a b r))‖ ≤
        Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
      ‖μ.cmean (fun a => (ν a).cmean (fun b => ∑ r, F a b r))‖ ≤
        Real.exp (-H*(bulkSize k L:ℝ)) := by
  filter_upwards [selected_root_error_eventually Bs BD Bz H hH hk,
    selected_root_error_bulk_eventually Bs BD Bz H hH hk] with L hfreq hbulk
  intro l hl α β _ _ μ ν F hF
  have h := nested_root_sum_error_le μ ν F (Real.exp (-Real.exp ((21/2000:ℝ)*L))) hF
  exact ⟨h.trans (hfreq l hl),h.trans (hbulk l hl)⟩

end Ostmann.Arithmetic.HistorySelectedRootErrorBudget

end

end OAI
