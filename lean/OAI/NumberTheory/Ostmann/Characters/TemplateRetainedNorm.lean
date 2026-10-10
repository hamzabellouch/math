import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceWeight

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

theorem retainedHistoryWeight_sq_le_supported (k j:ℕ)
    (B V:(l:ℕ)→State k (l+1)→ℤ)
    (extra:(l:ℕ)→ℤ→State k l→HistoryReconstruction.Tree l→Prop)
    (mask:(l:ℕ)→ℤ→State k l→Prop) (X Δ W:ℝ)
    (s:ℤ) (x:State k j) (t:HistoryReconstruction.Tree j) :
    ‖retainedHistoryWeight k B V extra mask X Δ W j s x t‖^2 ≤
      if UnitSupported k j s x t then ‖weight k mask X Δ W j s x t‖^2 else 0 := by
  by_cases h:TransferSupport k B V extra j s x t
  · simp only [retainedHistoryWeight,ite_eq_left h,ite_eq_left (h.unitSupported j),le_refl]
  · simp only [retainedHistoryWeight,ite_eq_right h,norm_zero,zero_pow (by decide : 2≠0)]
    split_ifs <;> positivity

end Ostmann.Characters.Template

end

end OAI
