import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyBudgetBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceLabels

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template
open HistoryFrequencyBudget

theorem stepHistoryRanges_actual (a m : ℝ) (j : ℕ) :
    stepHistoryRanges (ranges a m j) (signedRange (bound a m (j+1)))=
      ranges a m (j+1) := by
  funext p
  cases p with
  | nil => rfl
  | cons b p =>
    simp only [stepHistoryRanges,List.cons_ne_nil,ite_false,ranges,
      List.length_dropLast,List.length_cons]
    congr 2
    omega

end Ostmann.Characters.Template

end

end OAI
