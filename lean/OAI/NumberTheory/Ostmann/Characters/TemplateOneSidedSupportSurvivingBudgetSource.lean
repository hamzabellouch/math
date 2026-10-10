import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimatePivotHeight
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSourceHistory
import OAI.NumberTheory.Ostmann.Characters.OneSidedScaleGapAsymptotics
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSourceSyntax
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportSurvivingBudgetBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedSupportSurviving
open Template SymbolicHistory TemplateOneSidedBudget TemplateOneSidedRelabel
open TemplateOneSidedSupportTelescoping HigherBiasSource HigherBiasSource.SourceTemplate
open TemplateOneSidedSourceSyntax DiagonalEstimate InitialCharacterScale
open HistoryFrequencyLabels HistoryFrequencyBudget Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def sourceFamilySyntaxConstant (k : ℕ) : ℕ :=
  (1+∑j:Fin (k+1),obstructionSizeFactor k j.val)*(sourceExpressionConstant k+1)

theorem sourceFamilySyntaxConstant_pos (k : ℕ) : 0 < sourceFamilySyntaxConstant k := by
  unfold sourceFamilySyntaxConstant
  positivity

theorem actual_sourceFamilies_syntax
    {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (j : ℕ) (hj : j ≤ k) (P r : ℤ)
    (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
    (t : HistoryReconstruction.Tree j)
    (i : Σu:SurvivingSlot k j,Fin (survivingWidth k j (sourceWidth w.configuration (wordSize k L)) u))
    (q : Expr (Σu:SurvivingSlot k j,Fin (survivingWidth k j (sourceWidth w.configuration (wordSize k L)) u)))
    (hq : q∈actualFamilies k (survivingWidth k j (sourceWidth w.configuration (wordSize k L))) j
      (origins k j) r (groupedExpressions k j (sourceWidth w.configuration (wordSize k L)) P e) t i) :
    q.syntaxSize ≤ sourceFamilySyntaxConstant k*(wordSize k L+1) := by
  have he (u : (schedule k j).Slot) :
      (groupedExpressions k j (sourceWidth w.configuration (wordSize k L)) P e u).syntaxSize ≤
        sourceExpressionConstant k*(wordSize k L+1) := by
    change (relabel _ (survivingSampledExpressions _ _ _ _ _ u)).syntaxSize ≤ _
    rw [relabel_syntaxSize]
    exact actual_survivingSampledExpressions_syntaxSize w _ j P e u
  have hh := obstructionExpressions_size k j false r _ t _ he q
    (actualFamilies_obstructions _ _ _ _ _ _ _ false i q hq)
  have hfactor : obstructionSizeFactor k j ≤ 1+∑v:Fin (k+1),obstructionSizeFactor k v.val := by
    have hh := Finset.single_le_sum (f:=fun v:Fin (k+1)=>obstructionSizeFactor k v.val)
      (fun _ _=>Nat.zero_le _) (Finset.mem_univ (⟨j,by omega⟩:Fin (k+1)))
    exact hh.trans (Nat.le_add_left _ _)
  apply hh.trans
  calc
    _ ≤ (1+∑v:Fin (k+1),obstructionSizeFactor k v.val)*
        (sourceExpressionConstant k*(wordSize k L+1)+1) := Nat.mul_le_mul_right _ hfactor
    _ ≤ (1+∑v:Fin (k+1),obstructionSizeFactor k v.val)*
        ((sourceExpressionConstant k+1)*(wordSize k L+1)) :=
      Nat.mul_le_mul_left _ (by nlinarith)
    _ = _ := by unfold sourceFamilySyntaxConstant; rw [Nat.mul_assoc]

theorem eventually_actualFamilies_fixedLog (k : ℕ) (c β BD : ℝ)
    (hβ : -1 < β) (hBD : 0 ≤ BD) :
    ∀ᶠ L : ℝ in atTop, ∀ (d : Decomposition) (E : Finset ℕ) (δ α ρ γ c₀ : ℝ),
    ∀ (s : SelectedWordSource d E δ L k α β ρ γ c₀) (w : FixedConfigurationWitness s c BD)
      (j : ℕ), j < k → ∀ P∈DiagonalEstimate.sourcePivotRanges w j,
    ∀ (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
      (h : SourceHistory (k:=k) (L:=L) (BD:=BD) j)
      (i : Σu:SurvivingSlot k j,Fin (survivingWidth k j (sourceWidth w.configuration (wordSize k L)) u))
      (q : Expr (Σu:SurvivingSlot k j,Fin (survivingWidth k j (sourceWidth w.configuration (wordSize k L)) u))),
      q∈actualFamilies k (survivingWidth k j (sourceWidth w.configuration (wordSize k L))) j
        (origins k j) h.val.1 (groupedExpressions k j (sourceWidth w.configuration (wordSize k L)) P e)
        h.val.2 i → q.FixedLogBound (Real.exp ((β+1)*L)) := by
  let a := BD+20*Real.log (depthScale k)
  have ha : 0 ≤ a := add_nonneg hBD (mul_nonneg (by norm_num)
    (Real.log_nonneg (one_le_depthScale k)))
  have henvelope := eventually_historyPolynomialCost_le (linearEnvelope a k) (depthScale k) 1
    (depthScale_pos k).le (show 0 < β+1 by linarith) (by norm_num : (0:ℝ)<1)
  filter_upwards [sourcePivotRanges_height_eventually k c β hβ,henvelope,
    (wordSize_tendsto k).eventually_ge_atTop 1] with L hP henv hm
  intro d E δ α ρ γ c₀ s w j hj P hPr e h i q hq
  have hmono : linearEnvelope a j ≤ linearEnvelope a k := by
    have h2 : (2:ℝ)^j ≤ 2^k := pow_le_pow_right₀ (by norm_num) hj.le
    have h4 : (4:ℝ)^j ≤ 4^k := pow_le_pow_right₀ (by norm_num) hj.le
    unfold linearEnvelope
    nlinarith
  have hf : linearEnvelope a j*(wordSize k L:ℝ) ≤ Real.exp ((β+1)*L) := by
    have hh : linearEnvelope a k*(wordSize k L:ℝ) ≤ Real.exp ((β+1)*L) := by
      have henv' : linearEnvelope a k*(1+(wordSize k L:ℝ)) ≤ Real.exp ((β+1)*L) := by
        simpa only [historyPolynomialCost,pow_one,one_mul,wordSize] using henv
      nlinarith [linearEnvelope_pos ha k]
    exact (mul_le_mul_of_nonneg_right hmono (Nat.cast_nonneg _)).trans hh
  apply actualFamilies_surviving_fixedLog _ P e ha hm ?_ hf h.val.1 h.val.2 h.property i q hq
  have hh := hP d E δ α ρ γ c₀ BD s w j hj P hPr
  simpa only [abs_of_nonneg (show (0:ℝ) ≤ P from by positivity)] using hh

end Ostmann.Characters.TemplateOneSidedSupportSurviving

end

end OAI
