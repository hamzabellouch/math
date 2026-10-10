import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedBudgetFrequency
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSurvivingExpressionsSource
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportSurvivingFamilies

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedSupportSurviving
open Template SymbolicHistory TemplateOneSidedBudget TemplateOneSidedRelabel
open TemplateOneSidedSupportTelescoping HigherBiasSource HigherBiasSource.SourceTemplate
open HistoryFrequencyLabels HistoryFrequencyBudget
attribute [local instance] Classical.propDecidable

def survivingFamilySyntaxBudget {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) : ℕ :=
  obstructionSizeFactor k j*(survivingSourceSyntaxConstant cfg*(m+1)+1)

theorem actualFamilies_surviving_syntax {k : ℕ} (cfg : SourceConfiguration k)
    (m j : ℕ) (P s : ℤ)
    (e : Equiv.Perm (CopiedConstituent (schedule k j) j (sourceWidth cfg m)))
    (t : HistoryReconstruction.Tree j)
    (i : Σu:SurvivingSlot k j,Fin (survivingWidth k j (sourceWidth cfg m) u))
    (q : Expr (Σu:SurvivingSlot k j,Fin (survivingWidth k j (sourceWidth cfg m) u)))
    (hq : q∈actualFamilies k (survivingWidth k j (sourceWidth cfg m)) j (origins k j) s
      (groupedExpressions k j (sourceWidth cfg m) P e) t i) :
    q.syntaxSize ≤ survivingFamilySyntaxBudget cfg m j := by
  apply obstructionExpressions_size k j false s _ t _ ?_ q
    (actualFamilies_obstructions _ _ _ _ _ _ _ false i q hq)
  intro u
  change (relabel _ (survivingSampledExpressions _ _ _ _ _ u)).syntaxSize ≤ _
  rw [relabel_syntaxSize]
  exact survivingSampledExpressions_source_syntaxSize cfg m j P e u

theorem actualFamilies_surviving_fixedLog {k j : ℕ} (width : Role→ℕ)
    (P : ℕ+) (e : Equiv.Perm (CopiedConstituent (schedule k j) j width))
    {a m H : ℝ} (ha : 0 ≤ a) (hm : 1 ≤ m) (hP : (P:ℝ) ≤ Real.exp H)
    (hfrequency : linearEnvelope a j*m ≤ H) (s : ℤ) (t : HistoryReconstruction.Tree j)
    (ht : RangeSupported (ranges a m j) j [] s t)
    (i : Σu:SurvivingSlot k j,Fin (survivingWidth k j width u))
    (q : Expr (Σu:SurvivingSlot k j,Fin (survivingWidth k j width u)))
    (hq : q∈actualFamilies k (survivingWidth k j width) j (origins k j) s
      (groupedExpressions k j width P e) t i) : q.FixedLogBound H := by
  have hH : 0 ≤ H := (mul_nonneg (linearEnvelope_pos ha j).le (by linarith)).trans hfrequency
  apply obstructionExpressions_fixedBound k j (ranges a m j)
    (Real.one_le_exp_iff.mpr hH) ?_ [] false s _ t ?_ ht q
    (actualFamilies_obstructions _ _ _ _ _ _ _ false i q hq)
  · intro path z hz
    exact (actual_frequency_abs_le_exp ha hm j path z hz).trans
      (Real.exp_le_exp.mpr hfrequency)
  · intro u
    change (relabel _ (survivingSampledExpressions _ _ _ _ _ u)).FixedLogBound H
    rw [relabel_fixedLogBound]
    exact survivingSampledExpressions_fixedLogBound_pnat k j width P e hP u

end Ostmann.Characters.TemplateOneSidedSupportSurviving

end

end OAI
