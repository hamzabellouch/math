import OAI.NumberTheory.Ostmann.Characters.TemplateConstituentNormFixedBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Filter Construction Preliminaries HistoryFrequencyLabels HistoryFrequencyBudget
attribute [local instance] Classical.propDecidable

theorem fixed_pivot_retained_square_sum_eventually (j K : ℕ) (hj : j ≤ K)
    {z a α β c δ : ℝ} (hz : 0 < z) (ha : 0 < a) (hα : 0 < α)
    (hβ : 0 ≤ β) (hc : 0 ≤ c) (hδ : 0 < δ) (W : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ N : ℕ, ∀ E0 : Finset (PrimeUpTo N),
      ∀ _hE0 : 0 < primeShellMass E0,
      Real.exp (-c*L) ≤ primeShellMass E0 →
      (∀p ∈ E0,Real.exp (α*L) ≤ Real.log p.val) →
      (∀p ∈ E0,Real.log p.val ≤ Real.exp (β*L)) →
      ∀ k : ℕ, j < k → ∀ width : Role → ℕ, ∀ hw : 0 < width .word,
      ∀ E : (schedule k j).Constituent width → Finset (PrimeUpTo N),
      ∀ hE : ∀i,0 < primeShellMass (E i),
      (∀w,E (chosenPrimeIndex k j width hw w) = E0) →
      ∀ B V : (l : ℕ) → State k (l+1) → ℤ,
      ∀ extra : (l : ℕ) → ℤ → State k l → HistoryReconstruction.Tree l → Prop,
      ∀ mask : (l : ℕ) → ℤ → State k l → Prop, ∀ X : ℝ, 0 < X → ∀ P : ℤ,
      (outsidePrimePrior (schedule k j) j width E hE).mean (fun y =>
        (copiedPrimePrior (schedule k j) j width E hE).mean (fun h =>
          ∑t : SupportedHistory (ranges a (⌊z*L⌋₊ : ℝ) j) j [],
            ‖retainedHistoryWeight k B V extra mask X (a*(⌊z*L⌋₊ : ℝ)) W j t.val.1
              (sourceState k j P (copiedSampleState (schedule k j) j width h)
                (outsideSampleState (schedule k j) j width y)) t.val.2‖^2)) ≤
        Real.exp ((β+c+1)*(2:ℝ)^j*L+δ*(⌊z*L⌋₊ : ℝ)) := by
  filter_upwards [TemplateNormAsymptotic.retained_square_sum_eventually
    j K hj hz ha hα hβ hc hδ W] with L hL
  intro N E0 hE0 hZ hmin hmax k hjk width hw E hE hchosen B V extra mask X hX P
  let F : State k j → ℝ := fun C =>
    ∑t : SupportedHistory (ranges a (⌊z*L⌋₊ : ℝ) j) j [],
      ‖retainedHistoryWeight k B V extra mask X (a*(⌊z*L⌋₊ : ℝ)) W j t.val.1 C t.val.2‖^2
  change (outsidePrimePrior (schedule k j) j width E hE).mean (fun y =>
    (copiedPrimePrior (schedule k j) j width E hE).mean (fun h =>
      F (sourceState k j P (copiedSampleState (schedule k j) j width h)
        (outsideSampleState (schedule k j) j width y)))) ≤ _
  rw [←constituentPrimePrior_fixed_pivot_mean k j hjk width E hE P F]
  rw [constituentPrimePrior_chosen_binary_mean k j width hw E hE E0 hE0 hchosen
    (fun C => F (overwritePivot k j P C))]
  apply BinaryPriorExposure.outer_mean_le
  intro y
  simp only [overwritePivot_installWords]
  exact hL N (fun _ => E0) (fun _ => hE0) (fun _ => hZ)
    (fun _ => hmin) (fun _ => hmax) k (overwritePivot k j P (chosenContext k j width y))
    B V extra mask X hX

end Ostmann.Characters.Template

end

end OAI
