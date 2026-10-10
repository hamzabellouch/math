import OAI.NumberTheory.Ostmann.Characters.TemplateConstituentNorm
import OAI.NumberTheory.Ostmann.Characters.TemplateTerminalFrequency
import OAI.NumberTheory.Ostmann.Characters.TemplateTerminalUnitRoot

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Filter Construction Preliminaries HistoryFrequencyLabels HistoryFrequencyBudget
attribute [local instance] Classical.propDecidable

theorem unitTerminalRoot_norm_eventually (j K : ℕ) (hj : j≤K)
    {z a α β c δ : ℝ} (hz : 0<z) (ha : 0<a) (hα : 0<α)
    (hβ : 0≤β) (hc : 0≤c) (hδ : 0<δ) (W : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀N : ℕ, ∀E0 : Finset (PrimeUpTo N),
      ∀_hE0 : 0<primeShellMass E0,
      Real.exp (-c*L)≤primeShellMass E0 →
      (∀p∈E0,Real.exp (α*L)≤Real.log p.val) →
      (∀p∈E0,Real.log p.val≤Real.exp (β*L)) →
      ∀k : ℕ, ∀width : Role → ℕ, ∀hw : 0<width .word,
      ∀E : (schedule k j).Constituent width → Finset (PrimeUpTo N),
      ∀hE : ∀i,0<primeShellMass (E i),
      (∀w,E (chosenPrimeIndex k j width hw w)=E0) →
      (∀i p,p∈E i → Real.exp (α*L)≤Real.log p.val) →
      ∀ζ : PrimeUnitData (schedule k j) width N,
      (∀i p,‖ζ i p‖=1) →
      ∀χ : PrimeCharacterData (schedule k j) width N,
      (∀i p,p∈E i → χ i p≠1) →
      ∀centers : PrimeTranslationData (schedule k j) width N,
      ∀B V : (l:ℕ) → State k (l+1) → ℤ,
      ∀extra : (l:ℕ) → ℤ → State k l → HistoryReconstruction.Tree l → Prop,
      ∀mask : (l:ℕ) → ℤ → State k l → Prop, ∀X : ℝ, 0<X →
      (constituentPrimePrior (schedule k j) width E hE).mean (fun x =>
        ∑s : ↥(ranges a (⌊z*L⌋₊ : ℝ) j []),
          ‖unitTerminalRootIntegrand k j width ζ χ centers B V extra mask X
            (a*(⌊z*L⌋₊ : ℝ)) W (ranges a (⌊z*L⌋₊ : ℝ) j) x s‖^2) ≤
        Real.exp ((β+c+1)*(2:ℝ)^j*L+δ*(⌊z*L⌋₊ : ℝ)) := by
  filter_upwards [constituent_retained_square_sum_eventually j K hj hz ha hα hβ hc hδ W,
    terminalFrequencyCutoff_lt_prime_eventually hz hα ha.le j] with L hnorm hfreq
  intro N E0 hE0 hZ hmin hmax k width hw E hE hchosen hEmin ζ hζ χ hχ centers B V extra mask X hX
  apply le_trans (unitTerminalRootIntegrand_mean_norm_sq_le k j width ζ χ centers B V extra mask X
    (a*(⌊z*L⌋₊ : ℝ)) W (ranges a (⌊z*L⌋₊ : ℝ) j) E hE hζ hχ
    (fun i p hp => hfreq.2 p.val (primeUpTo_prime p) (hEmin i p hp)) hfreq.1)
  exact hnorm N E0 hE0 hZ hmin hmax k width hw E hE hchosen B V extra mask X hX

end Ostmann.Characters.Template

end

end OAI
