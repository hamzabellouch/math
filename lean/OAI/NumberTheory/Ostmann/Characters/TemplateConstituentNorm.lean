import OAI.NumberTheory.Ostmann.Characters.TemplateChosenPrimePrior
import OAI.NumberTheory.Ostmann.Characters.TemplateConstituentNormBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateNormAsymptotic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Filter Construction Preliminaries HistoryFrequencyLabels HistoryFrequencyBudget
attribute [local instance] Classical.propDecidable

theorem constituentPrimePrior_chosen_binary_mean (k j : ℕ) (width : Role → ℕ)
    (hw : 0 < width .word) {N : ℕ}
    (E : (schedule k j).Constituent width → Finset (PrimeUpTo N))
    (hE : ∀i,0 < primeShellMass (E i))
    (E0 : Finset (PrimeUpTo N)) (hE0 : 0 < primeShellMass E0)
    (hchosen : ∀w,E (chosenPrimeIndex k j width hw w)=E0)
    (F : State k j → ℝ) :
    (constituentPrimePrior (schedule k j) width E hE).mean
      (fun x=>F (constituentSampleState (schedule k j) width x)) =
      (productPrior (fun i : RemainingPrime k j width=>
        primeShellPrior (E i.val) (hE i.val))).mean (fun y=>
          BinaryPriorExposure.mean (fun _=>primeShellPrior E0 hE0) j []
            (fun x=>F (installWords k j (chosenContext k j width y)
              (chosenPrimeWords k j x)))) := by
  rw [constituentPrimePrior_chosen_mean k j width hw]
  have hprior : (fun w : WordSlot k j=>
      primeShellPrior (E (chosenPrimeIndex k j width hw w)) (hE _)) =
      (fun _ : WordSlot k j=>primeShellPrior E0 hE0) := by
    funext w
    congr 1
    exact hchosen w
  rw [hprior]
  apply congrArg (fun G=>
    (productPrior (fun i : RemainingPrime k j width=>
      primeShellPrior (E i.val) (hE i.val))).mean G)
  funext y
  simp_rw [constituentSampleState_assembleChosen k j width hw]
  rw [productPrior_wordTree_mean (primeShellPrior E0 hE0) k j []]
  rfl

theorem constituent_retained_square_sum_eventually (j K : ℕ) (hj : j ≤ K)
    {z a α β c δ : ℝ} (hz : 0 < z) (ha : 0 < a) (hα : 0 < α)
    (hβ : 0 ≤ β) (hc : 0 ≤ c) (hδ : 0 < δ) (W : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ N : ℕ, ∀ E0 : Finset (PrimeUpTo N),
      ∀ _hE0 : 0 < primeShellMass E0,
      Real.exp (-c*L) ≤ primeShellMass E0 →
      (∀p∈E0,Real.exp (α*L) ≤ Real.log p.val) →
      (∀p∈E0,Real.log p.val ≤ Real.exp (β*L)) →
      ∀ k : ℕ, ∀ width : Role → ℕ, ∀ hw : 0 < width .word,
      ∀ E : (schedule k j).Constituent width → Finset (PrimeUpTo N),
      ∀ hE : ∀i,0 < primeShellMass (E i),
      (∀w,E (chosenPrimeIndex k j width hw w)=E0) →
      ∀ B V : (l : ℕ) → State k (l+1) → ℤ,
      ∀ extra : (l : ℕ) → ℤ → State k l → HistoryReconstruction.Tree l → Prop,
      ∀ mask : (l : ℕ) → ℤ → State k l → Prop, ∀ X : ℝ, 0 < X →
      (constituentPrimePrior (schedule k j) width E hE).mean
        (fun x=>∑h : SupportedHistory (ranges a (⌊z*L⌋₊ : ℝ) j) j [],
          ‖retainedHistoryWeight k B V extra mask X (a*(⌊z*L⌋₊ : ℝ)) W j h.val.1
            (constituentSampleState (schedule k j) width x) h.val.2‖^2) ≤
        Real.exp ((β+c+1)*(2:ℝ)^j*L+δ*(⌊z*L⌋₊ : ℝ)) := by
  filter_upwards [TemplateNormAsymptotic.retained_square_sum_eventually
    j K hj hz ha hα hβ hc hδ W] with L hL
  intro N E0 hE0 hZ hmin hmax k width hw E hE hchosen B V extra mask X hX
  let F : State k j → ℝ := fun C=>
    ∑h : SupportedHistory (ranges a (⌊z*L⌋₊ : ℝ) j) j [],
      ‖retainedHistoryWeight k B V extra mask X (a*(⌊z*L⌋₊ : ℝ)) W j h.val.1 C h.val.2‖^2
  change (constituentPrimePrior (schedule k j) width E hE).mean
    (fun x=>F (constituentSampleState (schedule k j) width x)) ≤ _
  rw [constituentPrimePrior_chosen_binary_mean k j width hw E hE E0 hE0 hchosen F]
  apply BinaryPriorExposure.outer_mean_le
  intro y
  exact hL N (fun _=>E0) (fun _=>hE0) (fun _=>hZ)
    (fun _=>hmin) (fun _=>hmax) k (chosenContext k j width y) B V extra mask X hX

end Ostmann.Characters.Template

end

end OAI
