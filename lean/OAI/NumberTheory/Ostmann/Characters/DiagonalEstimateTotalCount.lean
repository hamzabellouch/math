import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateTotalCountBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Template HigherBiasSource HigherBiasSource.SourceTemplate HistoryFrequencyBudget
open HistoryFrequencyLabels TemplateOneSidedBudget InitialCharacterScale Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def totalCopiedLinearCoefficient (k : ℕ) : ℝ :=
  (2:ℝ)^k*(depthScale k+1+2*maxCells 4 k)

theorem totalCopiedLinearCoefficient_pos (k : ℕ) : 0 < totalCopiedLinearCoefficient k := by
  unfold totalCopiedLinearCoefficient maxCells
  have hz := depthScale_pos k
  positivity

theorem actualCopied_card_le_linear {k : ℕ} (cfg : SourceConfiguration k) {j : ℕ}
    (hj : j ≤ k) {L : ℝ} (hL : 1 ≤ L)
    (hc : (configCellCount cfg:ℝ) ≤ maxCells 4 k) :
    (Fintype.card (ActualCopied cfg (wordSize k L) j):ℝ) ≤ totalCopiedLinearCoefficient k*L := by
  have hn : (Fintype.card (ActualCopied cfg (wordSize k L) j):ℝ) ≤
      (2:ℝ)^j*((wordSize k L:ℝ)+1+2*(configCellCount cfg:ℝ)) := by
    exact_mod_cast actualCopied_card_le cfg (wordSize k L) j
  have hmax : 0 ≤ maxCells 4 k := by unfold maxCells; positivity
  have hz := (depthScale_pos k).le
  have hm := (wordSize_bounds k (by linarith : 0 ≤ L)).2
  have hp : (2:ℝ)^j ≤ 2^k := pow_le_pow_right₀ (by norm_num) hj
  calc
    _ ≤ (2:ℝ)^j*((wordSize k L:ℝ)+1+2*(configCellCount cfg:ℝ)) := hn
    _ ≤ (2:ℝ)^k*((wordSize k L:ℝ)+1+2*maxCells 4 k) :=
      mul_le_mul hp (by linarith) (by positivity) (by positivity)
    _ ≤ (2:ℝ)^k*((depthScale k+1+2*maxCells 4 k)*L) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hh := mul_le_mul_of_nonneg_left hL hmax
      nlinarith
    _ = _ := by unfold totalCopiedLinearCoefficient; ring

def totalCountConstant (k : ℕ) (BD : ℝ) : ℝ :=
  1+(totalCopiedLinearCoefficient k)^2+
    pairedHistoryCountCoefficient k (BD+20*Real.log (depthScale k))*(1+depthScale k)

theorem totalCountConstant_pos {BD : ℝ} (hBD : 0 ≤ BD) (k : ℕ) :
    0 < totalCountConstant k BD := by
  have hb : 0 ≤ BD+20*Real.log (depthScale k) :=
    add_nonneg hBD (mul_nonneg (by norm_num) (Real.log_nonneg (one_le_depthScale k)))
  have hh := pairedHistoryCountCoefficient_nonneg hb k
  have hz := (depthScale_pos k).le
  unfold totalCountConstant
  positivity

theorem total_count_le_exp {k : ℕ} (BD : ℝ) (hBD : 0 ≤ BD)
    {L : ℝ} (hL : 1 ≤ L) (hm : 1 ≤ (wordSize k L:ℝ))
    (cfg : SourceConfiguration k) {j : ℕ} (hj : j ≤ k)
    (hc : (configCellCount cfg:ℝ) ≤ maxCells 4 k) :
    (Fintype.card (Equiv.Perm (ActualCopied cfg (wordSize k L) j)):ℝ)*
      (Fintype.card (SupportedHistory
        (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j) j []):ℝ)^2 ≤
      Real.exp (totalCountConstant k BD*L^2) := by
  let b := BD+20*Real.log (depthScale k)
  let H := pairedHistoryCountCoefficient k b
  let C := totalCopiedLinearCoefficient k
  have hb : 0 ≤ b := add_nonneg hBD
    (mul_nonneg (by norm_num) (Real.log_nonneg (one_le_depthScale k)))
  have hH : 0 ≤ H := pairedHistoryCountCoefficient_nonneg hb k
  have hC : 0 < C := totalCopiedLinearCoefficient_pos k
  have hz := depthScale_pos k
  have hL0 : 0 ≤ L := by linarith
  have hLs : L ≤ L^2 := by nlinarith
  have hcard := actualCopied_card_le_linear cfg hj hL hc
  have hperm : (Fintype.card (Equiv.Perm (ActualCopied cfg (wordSize k L) j)):ℝ) ≤
      Real.exp (C^2*L^2) := by
    rw [Fintype.card_perm]
    apply (factorial_le_exp_sq _).trans
    apply Real.exp_le_exp.mpr
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
    simpa only [mul_pow] using hh
  have hhist := supportedHistory_pair_card_le_uniform hb hm hj
  have hhist' : (Fintype.card (SupportedHistory (ranges b (wordSize k L:ℝ) j) j []):ℝ)^2 ≤
      Real.exp (H*(1+depthScale k)*L^2) := by
    apply hhist.trans
    apply Real.exp_le_exp.mpr
    have hmup := (wordSize_bounds k hL0).2
    have hi : 1+(wordSize k L:ℝ) ≤ (1+depthScale k)*L := by nlinarith
    calc
      _ ≤ H*((1+depthScale k)*L) := mul_le_mul_of_nonneg_left hi hH
      _ ≤ H*((1+depthScale k)*L^2) := by gcongr
      _ = _ := by ring
  have hh := mul_le_mul hperm hhist' (sq_nonneg _) (Real.exp_pos _).le
  apply hh.trans
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  change C^2*L^2+H*(1+depthScale k)*L^2 ≤ (1+C^2+H*(1+depthScale k))*L^2
  nlinarith [sq_nonneg L]

theorem exists_total_count_constant (k : ℕ) (BD : ℝ) (hBD : 0 ≤ BD) :
    ∃ K : ℝ,0 < K ∧ ∀ᶠ L : ℝ in atTop,∀ j : ℕ,j ≤ k →
      ∀ cfg : SourceConfiguration k,(configCellCount cfg:ℝ) ≤ maxCells 4 k →
      (Fintype.card (Equiv.Perm (ActualCopied cfg (wordSize k L) j)):ℝ)*
        (Fintype.card (SupportedHistory
          (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j) j []):ℝ)^2 ≤
        Real.exp (K*L^2) := by
  refine ⟨totalCountConstant k BD,totalCountConstant_pos hBD k,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ),(wordSize_tendsto k).eventually_ge_atTop 1]
    with L hL hm
  intro j hj cfg hc
  exact total_count_le_exp BD hBD hL hm cfg hj hc

end Ostmann.Characters.DiagonalEstimate

end

end OAI
