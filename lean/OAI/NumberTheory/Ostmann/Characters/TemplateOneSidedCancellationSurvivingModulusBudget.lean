import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSurvivingModulus

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedBudget
open SymbolicHistory Template TemplateOneSidedCancellation HistoryFrequencyLabels HistoryFrequencyBudget
attribute [local instance] Classical.propDecidable

theorem residuePolynomialConstant_nonneg {a : ℝ} (ha : 0 ≤ a) (k j : ℕ) :
    0 ≤ residuePolynomialConstant a k j := by
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have he : 0 ≤ linearEnvelope a j := (linearEnvelope_pos ha j).le
  unfold residuePolynomialConstant
  positivity

def survivingPairModulusConstant (a : ℝ) (k j : ℕ) : ℝ :=
  2*residuePolynomialConstant a k j+1

theorem survivingPairModulusConstant_pos {a : ℝ} (ha : 0 ≤ a) (k j : ℕ) :
    0 < survivingPairModulusConstant a k j := by
  have h := residuePolynomialConstant_nonneg ha k j
  unfold survivingPairModulusConstant
  linarith

theorem surviving_historyPairResidueModulus_le_quartic_cost {a : ℝ} (ha : 0 ≤ a)
    (k j : ℕ) (z L : ℝ) (hm : 1 ≤ ⌊z*L⌋₊) (width : Role → ℕ) (P P' : ℤ)
    (e f : Equiv.Perm (CopiedConstituent (schedule k j) j width))
    (s v : ℤ) (t u : HistoryReconstruction.Tree j)
    (ht : RangeSupported (ranges a (⌊z*L⌋₊:ℝ) j) j [] s t)
    (hu : RangeSupported (ranges a (⌊z*L⌋₊:ℝ) j) j [] v u) :
    (historyPairResidueModulus k j s (survivingSampledExpressions k j width P e) t
      v (survivingSampledExpressions k j width P' f) u:ℝ) ≤
      Real.exp (historyPolynomialCost (survivingPairModulusConstant a k j) z 4 L) := by
  apply (surviving_historyPairResidueModulus_le_historyPolynomialCost ha k j z L hm
    width P P' e f s v t u ht hu).trans
  apply Real.exp_le_exp.mpr
  unfold historyPolynomialCost
  let M : ℝ := 1+(⌊z*L⌋₊:ℝ)
  have hM : 1 ≤ M := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hM0 : 0 ≤ M := by linarith
  have hC := (survivingPairModulusConstant_pos ha k j).le
  change 2*residuePolynomialConstant a k j*M^3 ≤ survivingPairModulusConstant a k j*M^4
  calc
    _ ≤ survivingPairModulusConstant a k j*M^3 :=
      mul_le_mul_of_nonneg_right (by unfold survivingPairModulusConstant; linarith)
        (pow_nonneg hM0 3)
    _ ≤ (survivingPairModulusConstant a k j*M^3)*M := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hM
        (mul_nonneg hC (pow_nonneg hM0 3))
    _ = _ := by ring

theorem exists_surviving_historyPairResidueModulus_budget {a : ℝ} (ha : 0 ≤ a)
    (k j : ℕ) : ∃ C : ℝ, 0 < C ∧
      ∀ (z L : ℝ), 1 ≤ ⌊z*L⌋₊ → ∀ (width : Role → ℕ) (P P' : ℤ)
        (e f : Equiv.Perm (CopiedConstituent (schedule k j) j width))
        (s v : ℤ) (t u : HistoryReconstruction.Tree j),
        RangeSupported (ranges a (⌊z*L⌋₊:ℝ) j) j [] s t →
        RangeSupported (ranges a (⌊z*L⌋₊:ℝ) j) j [] v u →
        (historyPairResidueModulus k j s (survivingSampledExpressions k j width P e) t
          v (survivingSampledExpressions k j width P' f) u:ℝ) ≤
          Real.exp (historyPolynomialCost C z 4 L) := by
  exact ⟨survivingPairModulusConstant a k j,survivingPairModulusConstant_pos ha k j,
    fun z L hm width P P' e f s v t u ht hu =>
      surviving_historyPairResidueModulus_le_quartic_cost ha k j z L hm width P P'
        e f s v t u ht hu⟩

end Ostmann.Characters.TemplateOneSidedBudget

end

end OAI
