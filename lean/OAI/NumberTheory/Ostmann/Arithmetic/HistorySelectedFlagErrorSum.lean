import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedFlagError

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryUnnormalizedFlagError
open Construction Conclusion HistorySymbolicEncoding HistoryPairPattern HistoryPairRows
open HistoryPairFlags HistoryPairRepresentatives Filter

theorem selected_flag_error_sum_eventually (Bs BD Bz N C : ℝ) (hN : 0 ≤ N)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ l ≤ k, ∀ (h g : History l),
      TreeSourceLabels (Template.initial (2*(bulkSize k L/2)) k) h →
      TreeSourceLabels (Template.initial (2*(bulkSize k L/2)) k) g →
      ∀ (outside : List ℕ), (∀p∈outside,0 < p) → outside.length ≤ bulkSize k L →
      (∀p∈outside,Real.log (p:ℝ) ≤ Real.exp ((1/1000:ℝ)*L)) →
      (∑ r : Representative h g, errorBudget
        ((outside.prod:ℝ)^(2^(l+1))*Real.exp (C*((bulkSize k L:ℝ)+1)))
        (((2*Fintype.card (Fiber h g r)+(Fintype.card (Fiber h g r))^2:ℕ):ℝ))
        (((4*degreeBudget h g:ℕ):ℝ))
        (max 0 (Real.log (envelope h g (frequencyBound Bs BD Bz k L)
          (HistorySignedResidues.actualFactorCap Bs BD Bz k L)))/Real.log 2)
        (Real.exp (N*L-Real.exp ((39/10000:ℝ)*L))) (Real.exp (N*L))
        (Fintype.card (HistoryPairPattern.PairKey h g))) ≤
          Real.exp (-Real.exp ((1/500:ℝ)*L)) := by
  let T := max (spectatorCost k C) (2*HistorySelectedFlagBudgets.selectedExponent Bs BD Bz k)
  have hT : 0 ≤ T := (spectatorCost_pos k C).le.trans (le_max_left _ _)
  filter_upwards [errorBudget_eventually N (coordinateGrowth k) T hN
    (coordinateGrowth_pos k).le hT,
    HistorySelectedFlagBudgets.selected_flag_budgets_eventually Bs BD Bz hk,
    eventually_ge_atTop (0:ℝ)] with L he hflags hL
  intro l hl h g hh hg outside hpos hlen hlog
  have hf := hflags (bulkSize k L/2) (Nat.div_le_self _ 2) l hl h g hh hg
  let J : Representative h g → ℝ := fun r =>
    ((2*Fintype.card (Fiber h g r)+(Fintype.card (Fiber h g r))^2:ℕ):ℝ)
  have hJF : (∑ r, J r) ≤
      Real.exp ((2*HistorySelectedFlagBudgets.selectedExponent Bs BD Bz k)*(L+1)) := by
    calc
      _ ≤ ∑ _r : Representative h g,
          Real.exp (HistorySelectedFlagBudgets.selectedExponent Bs BD Bz k*(L+1)) :=
        Finset.sum_le_sum (fun r _ => hf.2.2.1 r)
      _ = (Fintype.card (Representative h g):ℝ)*
          Real.exp (HistorySelectedFlagBudgets.selectedExponent Bs BD Bz k*(L+1)) := by simp
      _ ≤ Real.exp (HistorySelectedFlagBudgets.selectedExponent Bs BD Bz k*(L+1))*
          Real.exp (HistorySelectedFlagBudgets.selectedExponent Bs BD Bz k*(L+1)) :=
        mul_le_mul_of_nonneg_right hf.2.1 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hTflag : HistorySelectedFlagBudgets.selectedExponent Bs BD Bz k ≤ T := by
    have := HistorySelectedFlagBudgets.selectedExponent_pos Bs BD Bz k
    exact (by linarith : HistorySelectedFlagBudgets.selectedExponent Bs BD Bz k ≤
      2*HistorySelectedFlagBudgets.selectedExponent Bs BD Bz k).trans (le_max_right _ _)
  have hF : Real.exp (HistorySelectedFlagBudgets.selectedExponent Bs BD Bz k*(L+1)) ≤
      Real.exp (commonLogBudget T L) :=
    Real.exp_le_exp.mpr ((linear_le_commonLogBudget
      (HistorySelectedFlagBudgets.selectedExponent_pos Bs BD Bz k).le hL).trans
        (commonLogBudget_mono hTflag))
  have hJ : (∑ r, J r) ≤ Real.exp (commonLogBudget T L) := by
    apply hJF.trans
    apply Real.exp_le_exp.mpr
    exact (linear_le_commonLogBudget (by positivity [HistorySelectedFlagBudgets.selectedExponent_pos Bs BD Bz k]) hL).trans
      (commonLogBudget_mono (le_max_right _ _))
  have hA := (spectator_prefactor_le hl hL C outside hpos hlen hlog).trans
    (Real.exp_le_exp.mpr (commonLogBudget_mono
      (le_max_left (spectatorCost k C) (2*HistorySelectedFlagBudgets.selectedExponent Bs BD Bz k))))
  have hout := he _ _ _ _ _ (selected_pairKey_card_le hL hh hg hl)
    (by positivity) (Finset.sum_nonneg (fun r _ => Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    (div_nonneg (le_max_left _ _) (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)))
    hA hJ (hf.1.trans hF) (hf.2.2.2.trans hF)
  simpa only [errorBudget, Finset.mul_sum, Finset.sum_mul] using hout

end Ostmann.Arithmetic.HistoryUnnormalizedFlagError

end

end OAI
