import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceUnitAmplitude
import OAI.NumberTheory.Ostmann.Characters.TemplateTerminalRootNorm

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

section
variable (k j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (ζ : PrimeUnitData (schedule k j) width Q)
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (B V : (l:ℕ) → State k (l+1) → ℤ)
    (extra : (l:ℕ) → ℤ → State k l → HistoryReconstruction.Tree l → Prop)
    (mask : (l:ℕ) → ℤ → State k l → Prop) (X Δ W : ℝ)
    (S : List Bool → Finset ℤ)

def unitTerminalRootIntegrand
    (x : (schedule k j).Constituent width → PrimeUpTo Q) (s : ↥(S [])) : ℂ :=
  sampleUnitMultiplier (schedule k j) width ζ x *
    terminalRootIntegrand k j width χ a B V extra mask X Δ W S x s

theorem sum_unitTerminalRootIntegrand
    (x : (schedule k j).Constituent width → PrimeUpTo Q) :
    (∑s : ↥(S []),unitTerminalRootIntegrand k j width ζ χ a B V extra mask X Δ W S x s)=
      unitAmplitudeIntegrand k j width ζ χ a B V extra mask X Δ W S x := by
  simp only [unitTerminalRootIntegrand,←Finset.mul_sum,sum_terminalRootIntegrand,
    unitAmplitudeIntegrand]

theorem unitAmplitude_eq_terminalRootMean
    (E : (schedule k j).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀i,0<primeShellMass (E i)) :
    unitAmplitude k j width ζ χ a B V extra mask X Δ W S E hE =
      (constituentPrimePrior (schedule k j) width E hE).cmean (fun x =>
        ∑s : ↥(S []),unitTerminalRootIntegrand k j width ζ χ a B V extra mask X Δ W S x s) := by
  simp only [sum_unitTerminalRootIntegrand,unitAmplitude]

theorem norm_unitTerminalRootIntegrand (hζ : ∀i p,‖ζ i p‖=1)
    (x : (schedule k j).Constituent width → PrimeUpTo Q) (s : ↥(S [])) :
    ‖unitTerminalRootIntegrand k j width ζ χ a B V extra mask X Δ W S x s‖=
      ‖terminalRootIntegrand k j width χ a B V extra mask X Δ W S x s‖ := by
  rw [unitTerminalRootIntegrand,norm_mul,norm_sampleUnitMultiplier _ _ ζ hζ,one_mul]

theorem unitTerminalRootIntegrand_mean_norm_sq_le {F : ℕ}
    (E : (schedule k j).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀i,0<primeShellMass (E i)) (hζ : ∀i p,‖ζ i p‖=1)
    (hχ : ∀i p,p∈E i → χ i p≠1) (hF : ∀i p,p∈E i → F<p.val)
    (hS : ∀path f,f∈S path → f≠0 ∧ f.natAbs≤F) :
    (constituentPrimePrior (schedule k j) width E hE).mean (fun x =>
      ∑s : ↥(S []),‖unitTerminalRootIntegrand k j width ζ χ a B V extra mask X Δ W S x s‖^2) ≤
    (constituentPrimePrior (schedule k j) width E hE).mean (fun x =>
      ∑h : SupportedHistory S j [],‖retainedHistoryWeight k B V extra mask X Δ W j h.val.1
        (constituentSampleState (schedule k j) width x) h.val.2‖^2) := by
  simp only [norm_unitTerminalRootIntegrand k j width ζ χ a B V extra mask X Δ W S hζ]
  exact terminalRootIntegrand_mean_norm_sq_le k j width E hE χ hχ a hF B V extra mask X Δ W S hS

end
end Ostmann.Characters.Template

end

end OAI
