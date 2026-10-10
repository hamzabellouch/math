import OAI.NumberTheory.Ostmann.Characters.OneSidedScaleGapAsymptotics
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedBudgetDegree
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedBudgetHistoryCount
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedBudgetResidues
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedBudgetWindows

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedBudget
open SymbolicHistory Template TemplateOneSidedCancellation HistoryFrequencyLabels HistoryFrequencyBudget
attribute [local instance] Classical.propDecidable

def residuePolynomialConstant (a : ℝ) (k j : ℕ) : ℝ :=
  (residueCount k j:ℝ)*((5*(recursiveSizeFactor k j:ℝ))^2+
    5*(recursiveSizeFactor k j:ℝ)+1)*(Real.log 2+linearEnvelope a j)

private lemma cubic_budget {D H d A M : ℝ} (hD : 0 ≤ D) (hd : 0 ≤ d)
    (hA : 0 ≤ A) (hM : 1 ≤ M) (hDM : D ≤ d*M) (hH : H ≤ A*M) :
    (D^2+D+1)*H ≤ (d^2+d+1)*A*M^3 := by
  have hM0 : 0 ≤ M := by linarith
  have hM2 : M ≤ M^2 := by nlinarith
  have hM21 : 1 ≤ M^2 := by nlinarith
  have hD2 : D^2 ≤ (d*M)^2 := pow_le_pow_left₀ hD hDM 2
  have hdM := mul_le_mul_of_nonneg_left hM2 hd
  have hp : D^2+D+1 ≤ (d^2+d+1)*M^2 := by
    nlinarith
  calc
    _ ≤ (D^2+D+1)*(A*M) := mul_le_mul_of_nonneg_left hH (by positivity)
    _ ≤ ((d^2+d+1)*M^2)*(A*M) := mul_le_mul_of_nonneg_right hp (mul_nonneg hA hM0)
    _ = _ := by ring

theorem sampled_residueModulus_le_cubic_exp {a : ℝ} (ha : 0 ≤ a)
    (k j m : ℕ) (hm : 1 ≤ m) (width : Role → ℕ) (hw : ∀r,width r ≤ m+1)
    (s : ℤ) (t : HistoryReconstruction.Tree j)
    (ht : RangeSupported (ranges a (m:ℝ) j) j [] s t) :
    ((residueModulus (historyResidueGuards k j s (sampledExpressions k j width) t)).natAbs:ℝ) ≤
      Real.exp (residuePolynomialConstant a k j*(1+(m:ℝ))^3) := by
  let H : ℝ := Real.log 2+linearEnvelope a j*(m:ℝ)
  let D : ℕ := recursiveSizeFactor k j*(2*(m+2)+1)
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hA : 0 ≤ linearEnvelope a j := (linearEnvelope_pos ha j).le
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hH : Real.log 2 ≤ H := by
    dsimp only [H]
    exact le_add_of_nonneg_right (mul_nonneg hA (Nat.cast_nonneg m))
  have hH0 : 0 ≤ H := hl.trans hH
  have hB : 1 ≤ Real.exp H := Real.one_le_exp_iff.mpr hH0
  have hfreq : ∀p z,z∈ranges a (m:ℝ) j p → |(z:ℝ)| ≤ Real.exp H := by
    intro p z hz
    exact (actual_frequency_abs_le_exp ha hm' j p z hz).trans
      (Real.exp_le_exp.mpr (by dsimp only [H];linarith))
  have hfixed := historyResidueGuards_fixed k j (ranges a (m:ℝ) j) hB hfreq [] s
    (sampledExpressions k j width) t (sampledExpressions_fixedBound k j width hB) ht
  have hsize : ∀q∈historyResidueGuards k j s (sampledExpressions k j width) t,
      q.expression.syntaxSize ≤ D := by
    apply historyResidueGuards_size k j s _ t (2*(m+2))
    intro i
    exact (sampledExpressions_syntaxSize k j width i).trans
      (Nat.mul_le_mul_left 2 (Nat.add_le_add_right (hw _) 1))
  have hh := residueModulus_abs_le_exp
    (historyResidueGuards k j s (sampledExpressions k j width) t) D hH
    (fun q hq=>(hfixed q hq).1) hsize (fun q hq=>(hfixed q hq).2)
  rw [historyResidueGuards_length] at hh
  rw [natAbs_real]
  apply hh.trans
  apply Real.exp_le_exp.mpr
  have hDM : (D:ℝ) ≤ (5*(recursiveSizeFactor k j:ℝ))*(1+(m:ℝ)) := by
    dsimp only [D]
    push_cast
    nlinarith [Nat.cast_nonneg (α:=ℝ) (recursiveSizeFactor k j)]
  have hHM : H ≤ (Real.log 2+linearEnvelope a j)*(1+(m:ℝ)) := by
    dsimp only [H]
    nlinarith
  have hb := cubic_budget (Nat.cast_nonneg D) (by positivity : 0 ≤ 5*(recursiveSizeFactor k j:ℝ))
    (add_nonneg hl hA) (le_add_of_nonneg_right (Nat.cast_nonneg m) : (1:ℝ) ≤ 1+(m:ℝ)) hDM hHM
  have hx := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α:=ℝ) (residueCount k j))
  unfold residuePolynomialConstant
  nlinarith [hx]

theorem sampled_residueModulus_le_historyPolynomialCost {a : ℝ} (ha : 0 ≤ a)
    (k j : ℕ) (z L : ℝ) (hm : 1 ≤ ⌊z*L⌋₊)
    (width : Role → ℕ) (hw : ∀r,width r ≤ ⌊z*L⌋₊+1)
    (s : ℤ) (t : HistoryReconstruction.Tree j)
    (ht : RangeSupported (ranges a (⌊z*L⌋₊:ℝ) j) j [] s t) :
    ((residueModulus (historyResidueGuards k j s (sampledExpressions k j width) t)).natAbs:ℝ) ≤
      Real.exp (historyPolynomialCost (residuePolynomialConstant a k j) z 3 L) :=
  sampled_residueModulus_le_cubic_exp ha k j _ hm width hw s t ht

end Ostmann.Characters.TemplateOneSidedBudget

end

end OAI
