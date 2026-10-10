import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedFlagBudgetsActual
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedFlagBudgetsCountsExponential

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedFlagBudgets
open Construction HistorySymbolicEncoding HistoryPairFlags HistoryPairRows HistoryPairRepresentatives
open Conclusion Filter

def selectedExponent (Bs BD Bz : ℝ) (k : ℕ) : ℝ :=
  countExponent k*(bulkScale k+1)+envelopeExponent Bs BD Bz k (3/250)+1

theorem selectedExponent_pos (Bs BD Bz : ℝ) (k : ℕ) :
    0<selectedExponent Bs BD Bz k := by
  have hc := countExponent_pos k
  have he := envelopeExponent_pos Bs BD Bz k (3/250)
  have hb : 0 ≤ bulkScale k := by unfold bulkScale; positivity
  unfold selectedExponent
  positivity

theorem count_exp_le_selected (Bs BD Bz : ℝ) (k : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    Real.exp (countExponent k*((bulkSize k L:ℝ)+1)) ≤ 
      Real.exp (selectedExponent Bs BD Bz k*(L+1)) := by
  apply Real.exp_le_exp.mpr
  have hb : 0 ≤ bulkScale k := by unfold bulkScale; positivity
  have hm : (bulkSize k L:ℝ)+1 ≤ (bulkScale k+1)*(L+1) := by
    have hh := (bulkSize_bounds k hL).2
    nlinarith
  have hcm := mul_le_mul_of_nonneg_left hm (countExponent_pos k).le
  have he := envelopeExponent_pos Bs BD Bz k (3/250)
  unfold selectedExponent
  nlinarith

theorem selected_flag_budgets_eventually (Bs BD Bz : ℝ) {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop, ∀b ≤ bulkSize k L, ∀l ≤ k, ∀h g : History l,
      TreeSourceLabels (Template.initial (2*b) k) h  → 
      TreeSourceLabels (Template.initial (2*b) k) g  → 
      (((4*degreeBudget h g:ℕ):ℝ) ≤ Real.exp (selectedExponent Bs BD Bz k*(L+1))) ∧
      ((Fintype.card (Representative h g):ℝ) ≤ Real.exp (selectedExponent Bs BD Bz k*(L+1))) ∧
      (∀r : Representative h g,
        ((2*Fintype.card (Fiber h g r)+(Fintype.card (Fiber h g r))^2:ℕ):ℝ) ≤ 
          Real.exp (selectedExponent Bs BD Bz k*(L+1))) ∧
      (max 0 (Real.log (envelope h g (frequencyBound Bs BD Bz k L)
        (HistorySignedResidues.actualFactorCap Bs BD Bz k L)))/Real.log 2 ≤ 
          Real.exp (selectedExponent Bs BD Bz k*(L+1))) := by
  filter_upwards [selected_envelope_actualCap_eventually Bs BD Bz hk,
    eventually_ge_atTop (0:ℝ)] with L henv hL
  intro b hb l hl h g hh hg
  have hm : (0:ℝ) ≤ bulkSize k L := Nat.cast_nonneg _
  have hb' : (b:ℝ) ≤ bulkSize k L := Nat.cast_le.mpr hb
  have hcount := count_exp_le_selected Bs BD Bz k hL
  refine ⟨(four_degreeBudget_le_exp hh hg hl hm hb').trans hcount,
    (representative_card_le_exp hh hg hl hm hb').trans hcount,?_,?_⟩
  · intro r
    have hi := (index_card_le_exp hh hg hl hm hb' r).trans hcount
    simpa only [index_card] using hi
  · apply (henv b hb l hl h g hh hg).trans
    apply Real.exp_le_exp.mpr
    have hcc : 0 ≤ countExponent k*(bulkScale k+1) := by
      have hc := countExponent_pos k
      have hb0 : 0 ≤ bulkScale k := by unfold bulkScale; positivity
      positivity
    unfold selectedExponent
    nlinarith

end Ostmann.Arithmetic.HistorySelectedFlagBudgets

end

end OAI
