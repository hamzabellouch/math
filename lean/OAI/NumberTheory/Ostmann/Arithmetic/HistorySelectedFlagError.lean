import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedFlagBudgets
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryUnnormalizedFlagErrorGrowth

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryUnnormalizedFlagError
open Construction Conclusion HistorySymbolicEncoding HistoryPairPattern HistoryPairRows
open HistoryPairFlags HistoryPairRepresentatives Filter

theorem selected_flag_error_eventually (Bs BD Bz N C : ℝ) (hN : 0 ≤ N)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ l ≤ k, ∀ (h g : History l),
      TreeSourceLabels (Template.initial (2*(bulkSize k L/2)) k) h →
      TreeSourceLabels (Template.initial (2*(bulkSize k L/2)) k) g →
      ∀ (outside : List ℕ), (∀p∈outside,0 < p) → outside.length ≤ bulkSize k L →
      (∀p∈outside,Real.log (p:ℝ) ≤ Real.exp ((1/1000:ℝ)*L)) →
      ∀ r : Representative h g,
      errorBudget
        ((outside.prod:ℝ)^(2^(l+1))*Real.exp (C*((bulkSize k L:ℝ)+1)))
        (((2*Fintype.card (Fiber h g r)+(Fintype.card (Fiber h g r))^2:ℕ):ℝ))
        (((4*degreeBudget h g:ℕ):ℝ))
        (max 0 (Real.log (envelope h g (frequencyBound Bs BD Bz k L)
          (HistorySignedResidues.actualFactorCap Bs BD Bz k L)))/Real.log 2)
        (Real.exp (N*L-Real.exp ((39/10000:ℝ)*L))) (Real.exp (N*L))
        (Fintype.card (HistoryPairPattern.PairKey h g)) ≤
          Real.exp (-Real.exp ((1/500:ℝ)*L)) := by
  let T := max (spectatorCost k C) (HistorySelectedFlagBudgets.selectedExponent Bs BD Bz k)
  have hT : 0 ≤ T := (spectatorCost_pos k C).le.trans (le_max_left _ _)
  filter_upwards [errorBudget_eventually N (coordinateGrowth k) T hN
    (coordinateGrowth_pos k).le hT,
    HistorySelectedFlagBudgets.selected_flag_budgets_eventually Bs BD Bz hk,
    eventually_ge_atTop (0:ℝ)] with L he hflags hL
  intro l hl h g hh hg outside hpos hlen hlog r
  have hf := hflags (bulkSize k L/2) (Nat.div_le_self _ 2) l hl h g hh hg
  have hF : Real.exp (HistorySelectedFlagBudgets.selectedExponent Bs BD Bz k*(L+1)) ≤
      Real.exp (commonLogBudget T L) := by
    apply Real.exp_le_exp.mpr
    exact (linear_le_commonLogBudget
      (HistorySelectedFlagBudgets.selectedExponent_pos Bs BD Bz k).le hL).trans
        (commonLogBudget_mono (le_max_right _ _))
  have hA := (spectator_prefactor_le hl hL C outside hpos hlen hlog).trans
    (Real.exp_le_exp.mpr (commonLogBudget_mono (le_max_left (spectatorCost k C) (HistorySelectedFlagBudgets.selectedExponent Bs BD Bz k))))
  exact he _ _ _ _ _ (selected_pairKey_card_le hL hh hg hl)
    (by positivity) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (div_nonneg (le_max_left _ _) (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)))
    hA ((hf.2.2.1 r).trans hF) (hf.1.trans hF) (hf.2.2.2.trans hF)

end Ostmann.Arithmetic.HistoryUnnormalizedFlagError

end

end OAI
