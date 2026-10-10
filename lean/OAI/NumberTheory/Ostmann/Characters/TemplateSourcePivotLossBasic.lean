import OAI.NumberTheory.Ostmann.Characters.InitialCharacterStatisticScaleBasic
import OAI.NumberTheory.Ostmann.Characters.PivotProductNormalizationCells

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Filter InitialCharacterScale

def sourcePivotCountBound (k : ℕ) : ℝ := 2*Real.exp (2*((1/10000 : ℝ)*k))

def sourcePivotLoss (β : ℝ) (k : ℕ) (L : ℝ) (_j : ℕ) : ℝ :=
  (|β+1|+1)*sourcePivotCountBound k*L+(sourcePivotCountBound k)^2

theorem sourcePivotCountBound_pos (k : ℕ) : 0 < sourcePivotCountBound k := by
  unfold sourcePivotCountBound
  positivity

theorem sourcePivotLoss_nonneg (β : ℝ) (k : ℕ) {L : ℝ} (hL : 0 ≤ L) (j : ℕ) :
    0 ≤ sourcePivotLoss β k L j := by
  unfold sourcePivotLoss
  have := (sourcePivotCountBound_pos k).le
  positivity

theorem log_factorial_le_square (n : ℕ) : Real.log (n.factorial : ℝ) ≤ (n : ℝ)^2 := by
  by_cases hn : n=0
  · simp [hn]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ)<n by linarith)
  have hh := PivotProductNormalization.log_factorial_upper_all n
  rw [max_eq_left hn1] at hh
  have hm := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α:=ℝ) n)
  nlinarith

theorem pivot_factor_le_sourcePivotLoss {Q n : ℕ}
    (E : Fin n → Finset (Preliminaries.PrimeUpTo Q)) (β L c : ℝ) (k j : ℕ)
    (hc : 0 < c) (hL : 0 ≤ L) (hLc : -Real.log c ≤ L)
    (hcell : ∀i,c/Real.exp (β*L) ≤ primeShellMass (E i))
    (hn : (n : ℝ) ≤ sourcePivotCountBound k) :
    (n.factorial : ℝ)*PivotProductFibers.normalization E ≤ Real.exp (sourcePivotLoss β k L j) := by
  have hh := PivotProductNormalization.factor_le_exp_of_uniform_cells E c
    (fun _=>Real.exp (β*L)) β L hc (fun _=>Real.exp_pos _) hcell (fun _=>le_rfl) hLc
  apply hh.trans
  apply Real.exp_le_exp.mpr
  have hc' : β+1 ≤ |β+1|+1 := by linarith [le_abs_self (β+1)]
  have hcount : (β+1)*(n:ℝ)*L ≤ (|β+1|+1)*sourcePivotCountBound k*L := by
    apply mul_le_mul_of_nonneg_right _ hL
    exact (mul_le_mul_of_nonneg_right hc' (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hn (by positivity))
  have hsq : (n:ℝ)^2 ≤ (sourcePivotCountBound k)^2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hn 2
  have hfac := log_factorial_le_square n
  dsimp only [sourcePivotLoss]
  linarith

theorem eventually_pivot_leading_budget (β : ℝ) :
    ∀ᶠ k : ℕ in atTop,
      2*(k:ℝ)*(|β+1|+1)*sourcePivotCountBound k ≤ depthScale k := by
  filter_upwards [eventually_maxCells_le_depthScale (4*(|β+1|+1))] with k hk
  have hp := Real.exp_pos ((2/10000 : ℝ)*k)
  have hc : 0 ≤ |β+1|+1 := by positivity
  have he : 2*((1/10000 : ℝ)*k) = (2/10000 : ℝ)*k := by ring
  unfold sourcePivotCountBound
  rw [he]
  dsimp only [maxCells] at hk
  nlinarith

theorem eventually_sourcePivotLoss_budget (β : ℝ) :
    ∀ᶠ k : ℕ in atTop, ∀ᶠ L : ℝ in atTop, ∀n : ℕ, n ≤ k →
      (∑j∈Finset.range n,(sourcePivotLoss β k L j+Real.log 2)) ≤ (wordSize k L : ℝ) := by
  filter_upwards [eventually_pivot_leading_budget β] with k hk
  have ht := tendsto_id.const_mul_atTop (half_pos (depthScale_pos k))
  filter_upwards [ht.eventually_ge_atTop
      ((k:ℝ)*((sourcePivotCountBound k)^2+Real.log 2)+1),
    eventually_ge_atTop (0 : ℝ)] with L hL hL0
  intro n hn
  have hloss : 0 ≤ sourcePivotLoss β k L 0+Real.log 2 :=
    add_nonneg (sourcePivotLoss_nonneg β k hL0 0) (Real.log_nonneg (by norm_num))
  have hnR : (n:ℝ) ≤ k := by exact_mod_cast hn
  have hnk := mul_le_mul_of_nonneg_right hnR hloss
  have hlead := mul_le_mul_of_nonneg_right hk hL0
  have hfloor := (wordSize_bounds k hL0).1
  simp only [sourcePivotLoss,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  dsimp only [sourcePivotLoss] at hnk
  change (k:ℝ)*((sourcePivotCountBound k)^2+Real.log 2)+1 ≤ (depthScale k/2)*L at hL
  nlinarith

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI
