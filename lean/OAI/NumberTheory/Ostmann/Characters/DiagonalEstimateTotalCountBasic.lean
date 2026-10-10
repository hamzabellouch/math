import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateCopiedCodesCounts
import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticScaleBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedBudgetHistoryCount

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Template HigherBiasSource HigherBiasSource.SourceTemplate HistoryFrequencyBudget
open HistoryFrequencyLabels TemplateOneSidedBudget InitialCharacterScale Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem factorial_le_exp_sq (n : ℕ) : (n.factorial:ℝ) ≤ Real.exp ((n:ℝ)^2) := by
  have hf : (n.factorial:ℝ) ≤ (n:ℝ)^n := by exact_mod_cast n.factorial_le_pow
  have he : (n:ℝ) ≤ Real.exp (n:ℝ) := by linarith [Real.add_one_le_exp (n:ℝ)]
  apply hf.trans
  have hh := pow_le_pow_left₀ (Nat.cast_nonneg n) he n
  rw [←Real.exp_nat_mul] at hh
  simpa only [pow_two] using hh

def pairedHistoryCountCoefficient (k : ℕ) (b : ℝ) : ℝ :=
  ∑j∈Finset.range (k+1),2*(fullNodeCount j:ℝ)*(Real.log 2+linearEnvelope b j)

theorem pairedHistoryCountCoefficient_nonneg {b : ℝ} (hb : 0 ≤ b) (k : ℕ) :
    0 ≤ pairedHistoryCountCoefficient k b := by
  apply Finset.sum_nonneg
  intro j hj
  have he := (linearEnvelope_pos hb j).le
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  positivity

theorem paired_history_coefficient_le {b : ℝ} (hb : 0 ≤ b) {j k : ℕ} (hj : j ≤ k) :
    2*(fullNodeCount j:ℝ)*(Real.log 2+linearEnvelope b j) ≤ pairedHistoryCountCoefficient k b := by
  unfold pairedHistoryCountCoefficient
  apply Finset.single_le_sum (f := fun i : ℕ =>
    2*(fullNodeCount i:ℝ)*(Real.log 2+linearEnvelope b i)) (a := j)
  · intro i hi
    have he := (linearEnvelope_pos hb i).le
    have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hj)

theorem supportedHistory_pair_card_le_uniform {b m : ℝ} (hb : 0 ≤ b) (hm : 1 ≤ m)
    {j k : ℕ} (hj : j ≤ k) :
    (Fintype.card (SupportedHistory (ranges b m j) j []):ℝ)^2 ≤
      Real.exp (pairedHistoryCountCoefficient k b*(1+m)) := by
  have hh := supportedHistory_pair_card_le_exp hb hm j
  rw [Fintype.card_prod,Nat.cast_mul,←pow_two] at hh
  apply hh.trans
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
    (paired_history_coefficient_le hb hj) (by linarith))

theorem actualCopied_card_le {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) :
    Fintype.card (ActualCopied cfg m j) ≤ 2^j*(m+1+2*configCellCount cfg) := by
  rw [actualCopied_card]
  calc
    _ ≤ 2^j*(m+1)+2^j*(2*configCellCount cfg) :=
      Nat.add_le_add_left (copied_nonword_weight_le cfg m j) _
    _ = _ := by ring

end Ostmann.Characters.DiagonalEstimate

end

end OAI
