import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceFrequencySum
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceUnitSource
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeSourceUnits

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template.RetainedRow
open Construction HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

theorem frequencyPairCoefficient_mul {α γ : Type*} [Fintype α] [Fintype γ]
    (k j : ℕ) (B V : (j:ℕ) → State k (j+1) → ℤ)
    (extra : (j:ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (mask : (j:ℕ) → ℤ → State k j → Prop) (X Δ W : ℝ)
    (h : α → CopiedState k j) (y : γ → OutsideState k j)
    (S : List Bool → Finset ℤ) (path : List Bool) (R : Finset ℕ+)
    (phase : γ → ℕ+ → α → SupportedHistory S j path → ℂ) (U : γ → α → ℂ)
    (T : Finset ℤ) (a : γ) (x x' : α) (z z' : SupportedHistory S j path) (s : ℤ) :
    frequencyPairCoefficient k j B V extra mask X Δ W h y S path R
      (fun a P x z => U a x*phase a P x z) T a x x' z z' s =
      (U a x*conj (U a x')) * frequencyPairCoefficient k j B V extra mask X Δ W h y S path R
        phase T a x x' z z' s := by
  unfold frequencyPairCoefficient
  dsimp only
  split_ifs <;> simp only [pairCoefficient,term,map_mul,mul_zero]
  ring

end Ostmann.Characters.Template.RetainedRow
namespace Ostmann.Characters.Template

theorem sum_oldHistories_root {A : Type*} [AddCommMonoid A]
    (S : List Bool → Finset ℤ) (T : Finset ℤ) (j : ℕ)
    (F : ℤ → HistoryReconstruction.Tree (j+1) → A) :
    (∑l:HistoryFrequencyLabels.SupportedHistory S j [],
      ∑r:HistoryFrequencyLabels.SupportedHistory S j [],∑s∈T,
        F s ((l.val.1,r.val.1),l.val.2,r.val.2)) =
      ∑s∈T,∑l:HistoryFrequencyLabels.SupportedHistory S j [],
        ∑r:HistoryFrequencyLabels.SupportedHistory S j [],
          F s ((l.val.1,r.val.1),l.val.2,r.val.2) := by
  calc
    _ = ∑l:HistoryFrequencyLabels.SupportedHistory S j [],∑s∈T,
        ∑r:HistoryFrequencyLabels.SupportedHistory S j [],
          F s ((l.val.1,r.val.1),l.val.2,r.val.2) := by
      apply Finset.sum_congr rfl
      intro l hl
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

end Ostmann.Characters.Template

end

end OAI
