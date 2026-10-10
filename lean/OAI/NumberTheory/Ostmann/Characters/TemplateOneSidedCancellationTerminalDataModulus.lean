import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationTerminalDataSource
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedNumericInputs

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template TemplateOneSidedBudget TemplateOneSidedRelabel ParityActions
open HistoryFrequencyLabels HistoryFrequencyBudget TemplateOneSidedNumericInputs Filter

def terminalModulusCost (a : ℝ) (k n : ℕ) : ℝ :=
  2*residuePolynomialConstant a k (n+1)+1

theorem terminalModulusCost_pos {a : ℝ} (ha : 0 ≤ a) (k n : ℕ) :
    0 < terminalModulusCost a k n := by
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have he := (linearEnvelope_pos ha (n+1)).le
  unfold terminalModulusCost residuePolynomialConstant
  positivity

theorem terminalPair_modulus_le_cost {a : ℝ} (ha : 0 ≤ a)
    (k n : ℕ) (z L : ℝ) (hm : 1 ≤ ⌊z*L⌋₊)
    (width : Role → ℕ) (hw : ∀r,width r ≤ ⌊z*L⌋₊+1)
    (mWord : ℕ) (hmWord : mWord ≤ width .word)
    (σ π : Reassignments k n mWord) (s v : ℤ)
    (t u : HistoryReconstruction.Tree (n+1))
    (ht : RangeSupported (ranges a (⌊z*L⌋₊:ℝ) (n+1)) (n+1) [] s t)
    (hu : RangeSupported (ranges a (⌊z*L⌋₊:ℝ) (n+1)) (n+1) [] v u) :
    (historyPairResidueModulus k (n+1) s (paritySampledExpressions k n width mWord hmWord σ) t
      v (paritySampledExpressions k n width mWord hmWord π) u:ℝ) ≤
      Real.exp (historyPolynomialCost (terminalModulusCost a k n) z 4 L) := by
  have ht' := permutedSampled_residueModulus_le_historyPolynomialCost ha k (n+1) z L hm width hw
    (OneSidedPhase.prefixConstituentPermutation k n width mWord hmWord σ) s t ht
  have hu' := permutedSampled_residueModulus_le_historyPolynomialCost ha k (n+1) z L hm width hw
    (OneSidedPhase.prefixConstituentPermutation k n width mWord hmWord π) v u hu
  have hp := pair_modulus_budget _ _ z L 3 _ _ ht' hu'
  change (historyPairResidueModulus k (n+1) s (paritySampledExpressions k n width mWord hmWord σ) t
    v (paritySampledExpressions k n width mWord hmWord π) u:ℝ) ≤ _ at hp
  apply hp.trans
  apply Real.exp_le_exp.mpr
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have he := (linearEnvelope_pos ha (n+1)).le
  have hC : 0 ≤ residuePolynomialConstant a k (n+1) := by
    unfold residuePolynomialConstant
    positivity
  have hM : 1 ≤ 1+(⌊z*L⌋₊:ℝ) := by linarith [Nat.cast_nonneg (α:=ℝ) ⌊z*L⌋₊]
  have hpow : (1+(⌊z*L⌋₊:ℝ))^3 ≤ (1+(⌊z*L⌋₊:ℝ))^4 :=
    pow_le_pow_right₀ hM (by omega)
  have hmul := mul_le_mul_of_nonneg_left hpow (add_nonneg hC hC)
  unfold historyPolynomialCost terminalModulusCost
  nlinarith [pow_nonneg (le_trans zero_le_one hM) 4]

theorem eventually_terminal_frequency_height {a z β : ℝ} (ha : 0 ≤ a)
    (hz : 0 ≤ z) (hβ : 0 < β) (k n : ℕ) :
    ∀ᶠL : ℝ in atTop,linearEnvelope a (n+1)*(⌊z*L⌋₊:ℝ) ≤
      rowLogHeight (terminalModulusCost a k n) z β L := by
  filter_upwards [eventually_linear_frequency_height (linearEnvelope a (n+1)) z β
    (linearEnvelope_pos ha (n+1)).le hz hβ] with L hL
  exact hL _ (terminalModulusCost_pos ha k n).le

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
