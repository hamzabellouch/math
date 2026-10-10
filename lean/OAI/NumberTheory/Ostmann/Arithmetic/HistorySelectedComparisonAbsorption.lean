import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedComparisonAbsorptionBasic
import OAI.NumberTheory.Ostmann.Construction.LevelZeroFrequencyReserve

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistorySelectedComparisonAbsorption
open Construction Conclusion Filter

theorem selected_universal_absorption_eventually (Bs : ℝ) (hBs : 0 ≤ Bs)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop,∀l : ℕ,∀e : ℝ,e ≤ 1 →
      Real.exp ((2:ℝ)^l*(initialGap Bs k L+16*(bulkSize k L:ℝ)))+e ≤
      Real.exp ((2:ℝ)^l*(initialGap Bs k L+17*(bulkSize k L:ℝ))) := by
  filter_upwards [(bulkSize_tendsto_atTop hk).eventually_ge_atTop 1] with L hm
  intro l e he
  simpa only [show (16:ℝ)+1=17 by norm_num] using
    universal_main_add_residual_le (r:=(2:ℝ)^l)
    (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
    (initialGap_nonneg Bs hBs hk L) (by norm_num : (0:ℝ) ≤ 16) hm he

theorem selected_sum_decay_eventually (Bs BD Bz H : ℝ) {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop,∀l : ℕ,∀(ι : Type) [Fintype ι],∀F : ι→ℝ,
      (∀i,F i ≤ Real.exp (-frequencyBudget Bs BD Bz k L l-
        (H+(Fintype.card ι:ℝ))*(bulkSize k L:ℝ))) →
      ∑i,F i ≤ Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) := by
  filter_upwards [(bulkSize_tendsto_atTop hk).eventually_ge_atTop 1] with L hm
  intro l ι _ F hF
  apply finite_sum_exp_reserve_le F _ _ hm
  intro i
  convert hF i using 1; congr 1; ring

theorem selected_sum_bulk_decay_eventually (H : ℝ) {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop,∀(ι : Type) [Fintype ι],∀F : ι→ℝ,
      (∀i,F i ≤ Real.exp (-(H+(Fintype.card ι:ℝ))*(bulkSize k L:ℝ))) →
      ∑i,F i ≤ Real.exp (-H*(bulkSize k L:ℝ)) := by
  filter_upwards [(bulkSize_tendsto_atTop hk).eventually_ge_atTop 1] with L hm
  intro ι _ F hF
  apply finite_sum_exp_reserve_le F _ _ hm
  intro i
  convert hF i using 1; congr 1; ring

end Ostmann.Arithmetic.HistorySelectedComparisonAbsorption

end

end OAI
