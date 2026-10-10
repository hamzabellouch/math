import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantFrequencyCount
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedPatternFlagErrorCounts
import OAI.NumberTheory.Ostmann.Arithmetic.ScaleBudget

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistorySelectedPatternFlagError
open Construction CompensationEqualityPatterns Conclusion HistoryGiantFrequencyCount Filter
attribute [local instance] Classical.propDecidable

theorem pattern_frequency_card_le (Bs BD Bz : ℝ) (m k : ℕ) {L : ℝ}
    (hL : 1 ≤ L) (hm : 1 ≤ bulkSize k L) {l : ℕ} (hl : l ≤ k) :
    (Fintype.card (FrequencyChoices (frequencyBound Bs BD Bz k L) l ×
      FrequencyChoices (frequencyBound Bs BD Bz k L) l):ℝ)*
      Fintype.card (Pattern (pairedHistoryType (Template.initial m k) l)) ≤ 
        Real.exp ((actualFrequencyCost Bs BD Bz k+patternLogCost k)*L) := by
  have hf := actual_pair_card_le Bs BD Bz k L (by linarith) hm hl
  have hp := pattern_card_le_exp m k l hl
  calc
    _  ≤  Real.exp (actualFrequencyCost Bs BD Bz k*L)*Real.exp (patternLogCost k) :=
      mul_le_mul hf hp (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (actualFrequencyCost Bs BD Bz k*L+patternLogCost k) := (Real.exp_add _ _).symm
    _  ≤  _ := Real.exp_le_exp.mpr (by
      have hh := le_mul_of_one_le_right (patternLogCost_nonneg k) hL
      nlinarith)

theorem linear_frequency_cost_absorption (C : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (C*L)*Real.exp (-Real.exp ((1/500:ℝ)*L)) ≤ 
        Real.exp (-Real.exp ((3/2000:ℝ)*L)) := by
  filter_upwards [ScaleBudget.eventually_double_exp_error C 1
    (by norm_num : (0:ℝ)<1/500) (by norm_num : (3/2000:ℝ)<1/500)
    (by norm_num : (0:ℝ)<1)] with L hL
  convert hL using 1; simp only [pow_one,zero_mul,Real.exp_zero,mul_one,neg_mul,one_mul]
  rw [←Real.exp_add]
  congr 1
  ring

theorem pattern_frequency_error_eventually (Bs BD Bz : ℝ) {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop, ∀m l : ℕ, l ≤ k  → 
      ∀F : FrequencyChoices (frequencyBound Bs BD Bz k L) l  → 
        FrequencyChoices (frequencyBound Bs BD Bz k L) l  → 
        Pattern (pairedHistoryType (Template.initial m k) l)  →  ℝ,
      (∀f g p,F f g p ≤ Real.exp (-Real.exp ((1/500:ℝ)*L)))  → 
      (∑f,∑g,∑p,F f g p) ≤ Real.exp (-Real.exp ((3/2000:ℝ)*L)) := by
  filter_upwards [linear_frequency_cost_absorption
      (actualFrequencyCost Bs BD Bz k+patternLogCost k),
    (bulkSize_tendsto_atTop hk).eventually_ge_atTop 1,eventually_ge_atTop (1:ℝ)] with L habs hm hL
  intro m l hl F hF
  have hc := pattern_frequency_card_le Bs BD Bz m k hL (by exact_mod_cast hm) hl
  calc
    _  ≤  ∑_f:FrequencyChoices (frequencyBound Bs BD Bz k L) l,
        ∑_g:FrequencyChoices (frequencyBound Bs BD Bz k L) l,
        ∑_p:Pattern (pairedHistoryType (Template.initial m k) l),
          Real.exp (-Real.exp ((1/500:ℝ)*L)) :=
      Finset.sum_le_sum (fun f _=>Finset.sum_le_sum (fun g _=>Finset.sum_le_sum (fun p _=>hF f g p)))
    _ = ((Fintype.card (FrequencyChoices (frequencyBound Bs BD Bz k L) l ×
        FrequencyChoices (frequencyBound Bs BD Bz k L) l):ℝ)*
        Fintype.card (Pattern (pairedHistoryType (Template.initial m k) l)))*
        Real.exp (-Real.exp ((1/500:ℝ)*L)) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_prod,Nat.cast_mul]
      ring
    _  ≤  Real.exp ((actualFrequencyCost Bs BD Bz k+patternLogCost k)*L)*
        Real.exp (-Real.exp ((1/500:ℝ)*L)) :=
      mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)
    _  ≤  _ := habs

end Ostmann.Arithmetic.HistorySelectedPatternFlagError

end

end OAI
