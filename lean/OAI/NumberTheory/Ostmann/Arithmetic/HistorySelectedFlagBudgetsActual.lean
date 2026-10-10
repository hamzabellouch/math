import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedFlagBudgetsNumerics
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulusActualScales

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedFlagBudgets
open Construction HistorySymbolicEncoding HistoryPairFlags Conclusion Filter

def envelopeExponent (Bs BD Bz : ℝ) (k : ℕ) (a : ℝ) : ℝ :=
  (logarithmicCoefficient k (scaleLinearConstant Bs BD Bz k)+2)*(bulkScale k+1)+|a|+1

theorem envelopeExponent_pos (Bs BD Bz : ℝ) (k : ℕ) (a : ℝ) :
    0<envelopeExponent Bs BD Bz k a := by
  have hc := logarithmicCoefficient_nonneg k (scaleLinearConstant_pos Bs BD Bz k).le
  have hb : 0 ≤ bulkScale k := by unfold bulkScale; positivity
  unfold envelopeExponent
  positivity

theorem selected_envelope_log_le_exp (Bs BD Bz : ℝ) (k : ℕ) {L a B : ℝ}
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hm : 1 ≤ bulkSize k L) (hB : 1 ≤ B)
    (hlogB : Real.log B ≤ Real.exp (a*L))
    {b l : ℕ} (hb : b ≤ bulkSize k L) (hl : l ≤ k) {h g : History l}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) :
    max 0 (Real.log (envelope h g (frequencyBound Bs BD Bz k L) B))/Real.log 2 ≤ 
      Real.exp (envelopeExponent Bs BD Bz k a*(L+1)) := by
  have hbase := envelope_log_div_le_exp (frequencyBound Bs BD Bz k L) hh hg hl hB
    (scaleLinearConstant_pos Bs BD Bz k).le (Nat.cast_nonneg (bulkSize k L))
    (Nat.cast_le.mpr hb) (mul_nonneg ha hL)
    (selected_frequencyBound_log_le Bs BD Bz k L hm hl) hlogB
  apply hbase.trans (Real.exp_le_exp.mpr ?_)
  have hc := logarithmicCoefficient_nonneg k (scaleLinearConstant_pos Bs BD Bz k).le
  have hb0 : 0 ≤ bulkScale k := by unfold bulkScale; positivity
  have hmL : (bulkSize k L:ℝ)+1 ≤ (bulkScale k+1)*(L+1) := by
    have hh := (bulkSize_bounds k hL).2
    nlinarith
  have he := mul_le_mul_of_nonneg_left hmL (by linarith :
    0 ≤ logarithmicCoefficient k (scaleLinearConstant Bs BD Bz k)+2)
  unfold envelopeExponent
  rw [abs_of_nonneg ha]
  nlinarith

theorem selected_envelope_broad_height (Bs BD Bz : ℝ) (k : ℕ) {L : ℝ}
    (hL : 0 ≤ L) (hm : 1 ≤ bulkSize k L)
    {b l : ℕ} (hb : b ≤ bulkSize k L) (hl : l ≤ k) {h g : History l}
    (hh : TreeSourceLabels (Template.initial (2*b) k) h)
    (hg : TreeSourceLabels (Template.initial (2*b) k) g) :
    max 0 (Real.log (envelope h g (frequencyBound Bs BD Bz k L)
      (Real.exp (Real.exp ((19/20:ℝ)*L)))))/Real.log 2 ≤ 
      Real.exp (envelopeExponent Bs BD Bz k (19/20)*(L+1)) :=
  selected_envelope_log_le_exp Bs BD Bz k hL (by norm_num) hm
    (Real.one_le_exp (Real.exp_nonneg _)) (by rw [Real.log_exp]) hb hl hh hg

theorem actualFactorCap_log_le_eventually (Bs BD Bz : ℝ) (k : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      Real.log (HistorySignedResidues.actualFactorCap Bs BD Bz k L) ≤ Real.exp ((3/250:ℝ)*L) := by
  filter_upwards [HistorySignedResidues.actual_log_budget_eventually Bs BD Bz k 1 (by norm_num)] with L hL
  have hlog := Real.log_nonneg (HistorySignedResidues.actualFactorCap_one_le Bs BD Bz k L)
  have hcount : 1 ≤ (HistorySignedResidues.actualFactorCount k L:ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
  exact (le_mul_of_one_le_left hlog hcount).trans (by simpa only [one_mul] using hL)

theorem selected_envelope_actualCap_eventually (Bs BD Bz : ℝ) {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop, ∀b ≤ bulkSize k L, ∀l ≤ k, ∀h g : History l,
      TreeSourceLabels (Template.initial (2*b) k) h  → 
      TreeSourceLabels (Template.initial (2*b) k) g  → 
      max 0 (Real.log (envelope h g (frequencyBound Bs BD Bz k L)
        (HistorySignedResidues.actualFactorCap Bs BD Bz k L)))/Real.log 2 ≤ 
        Real.exp (envelopeExponent Bs BD Bz k (3/250)*(L+1)) := by
  filter_upwards [actualFactorCap_log_le_eventually Bs BD Bz k,
    (bulkSize_tendsto_atTop hk).eventually_ge_atTop 1,eventually_ge_atTop (0:ℝ)] with L hcap hm hL
  intro b hb l hl h g hh hg
  have hm' : 1 ≤ bulkSize k L := by exact_mod_cast hm
  exact selected_envelope_log_le_exp Bs BD Bz k hL (by norm_num) hm'
    (HistorySignedResidues.actualFactorCap_one_le Bs BD Bz k L) hcap hb hl hh hg

end Ostmann.Arithmetic.HistorySelectedFlagBudgets

end

end OAI
