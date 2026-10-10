import OAI.NumberTheory.Ostmann.Arithmetic.CompensationEqualityPatternsHistory
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationNormalizationBudgetCounts
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationNormalizationBudgetScales

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedPatternFlagError
open Construction CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryCompensationNormalizationBudget
attribute [local instance] Classical.propDecidable

local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) :=
  Classical.decEq _

def patternCount (k : ℕ) : ℕ := 2^(occurrenceCount k*occurrenceCount k)

theorem patternCount_pos (k : ℕ) : 0 < patternCount k := by
  unfold patternCount
  positivity

theorem pattern_card_le (m k l : ℕ) (hl : l ≤ k) :
    Fintype.card (Pattern (pairedHistoryType (Template.initial m k) l)) ≤ patternCount k := by
  have hc := card_pattern_le (pairedHistoryType (Template.initial m k) l)
  rw [paired_internal_card m k l hl] at hc
  change Fintype.card (Pattern (pairedHistoryType (Template.initial m k) l)) ≤
    2^(occurrenceCount l*occurrenceCount l) at hc
  apply hc.trans
  exact Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:ℕ))
    (Nat.mul_le_mul (occurrenceCount_mono hl) (occurrenceCount_mono hl))

theorem pattern_card_le_real (m k l : ℕ) (hl : l ≤ k) :
    (Fintype.card (Pattern (pairedHistoryType (Template.initial m k) l)):ℝ) ≤ (patternCount k:ℝ) := by
  exact_mod_cast pattern_card_le m k l hl

def patternLogCost (k : ℕ) : ℝ := (occurrenceCount k:ℝ)^2*Real.log 2

theorem patternLogCost_nonneg (k : ℕ) : 0 ≤ patternLogCost k := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold patternLogCost
  positivity

theorem patternCount_cast_eq_exp (k : ℕ) :
    (patternCount k:ℝ) = Real.exp (patternLogCost k) := by
  simp only [patternCount,Nat.cast_pow,Nat.cast_ofNat]
  conv_lhs => rw [show (2:ℝ) = Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num)]]
  rw [←Real.exp_nat_mul]
  congr 1
  simp only [patternLogCost,Nat.cast_mul,pow_two]

theorem pattern_card_le_exp (m k l : ℕ) (hl : l ≤ k) :
    (Fintype.card (Pattern (pairedHistoryType (Template.initial m k) l)):ℝ) ≤
      Real.exp (patternLogCost k) :=
  (pattern_card_le_real m k l hl).trans_eq (patternCount_cast_eq_exp k)

end Ostmann.Arithmetic.HistorySelectedPatternFlagError

end

end OAI
