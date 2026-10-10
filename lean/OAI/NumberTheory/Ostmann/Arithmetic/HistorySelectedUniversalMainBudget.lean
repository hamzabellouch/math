import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedUniversalMainBudgetBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedUniversalMainBudget
open Construction Conclusion HistoryProductWindows Filter

theorem selected_universal_main_budget_eventually (Bs : ℝ) {k : ℕ} (hk : 2 ≤ k) :
    ∀ᶠ L : ℝ in atTop, ∀l ≤ k,
      let m : ℕ := bulkSize k L
      let b : ℕ := m/2
      let r : ℕ := 2^l
      let A := Real.exp ((nominalInheritedWidth k l+2)+nominalRemovedWidth k l)*
        Real.exp (-(r:ℝ)*initialGap Bs k L+sourceXiConstant l k (2+2*(k:ℝ)))
      64*A*(2:ℝ)^(r*(2*b))*(3:ℝ)^(r*(2*b))*
        Real.exp (2*(r:ℝ)*(m:ℝ))*Real.exp (2*(r:ℝ)*initialGap Bs k L+(m:ℝ)) ≤ 
          Real.exp ((r:ℝ)*(initialGap Bs k L+16*(m:ℝ))) := by
  filter_upwards [fixed_cost_eventually (show 0<k by omega)] with L hfixed
  intro l hl
  dsimp only
  apply scalar_main_product_le (Nat.cast_nonneg (bulkSize k L))
    (one_le_pow₀ (by norm_num : 1 ≤ (2:ℕ))) _ (hfixed l hl)
  exact_mod_cast (show 2*(bulkSize k L/2) ≤ bulkSize k L by omega)

theorem selected_universal_main_budget_expanded (Bs : ℝ) {k : ℕ} (hk : 2 ≤ k) :
    ∀ᶠ L : ℝ in atTop, ∀l ≤ k,
      64*(Real.exp ((nominalInheritedWidth k l+2)+nominalRemovedWidth k l)*
        Real.exp (-((2^l:ℕ):ℝ)*initialGap Bs k L+sourceXiConstant l k (2+2*(k:ℝ))))*
      (2:ℝ)^(2^l*(2*(bulkSize k L/2)))*(3:ℝ)^(2^l*(2*(bulkSize k L/2)))*
      Real.exp (2*((2^l:ℕ):ℝ)*(bulkSize k L:ℝ))*
      Real.exp (2*((2^l:ℕ):ℝ)*initialGap Bs k L+(bulkSize k L:ℝ)) ≤ 
        Real.exp (((2^l:ℕ):ℝ)*(initialGap Bs k L+16*(bulkSize k L:ℝ))) :=
  selected_universal_main_budget_eventually Bs hk

end Ostmann.Arithmetic.HistorySelectedUniversalMainBudget

end

end OAI
