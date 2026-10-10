import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrencePrimeSizeFrequency
import OAI.NumberTheory.Ostmann.Characters.TemplateTerminalRoot

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

theorem norm_sampledHistoryPhase_of_mass_ne_zero (k j : ℕ) (width : Role → ℕ)
    {Q F : ℕ} (E : (schedule k j).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀i,0<primeShellMass (E i))
    (χ : PrimeCharacterData (schedule k j) width Q)
    (hχ : ∀i p,p∈E i → χ i p≠1)
    (a : PrimeTranslationData (schedule k j) width Q)
    (hF : ∀i p,p∈E i → F<p.val)
    (S : List Bool → Finset ℤ) (hS : ∀path f,f∈S path → f≠0 ∧ f.natAbs≤F)
    (x : (schedule k j).Constituent width → PrimeUpTo Q)
    (hx : (constituentPrimePrior (schedule k j) width E hE).mass x≠0)
    (hp : samplePrimeSupport (schedule k j) width x)
    (h : SupportedHistory S j []) :
    ‖sampledHistoryPhase k j width χ a x h.val.1 h.val.2‖=1 := by
  let : ∀i,Fact (x i).val.Prime := fun i => ⟨primeUpTo_prime (x i)⟩
  apply norm_actualHistoryPhase k j width (fun i => (x i).val) hp
  · intro i
    exact hχ i (x i) (primeProductPrior_mem_of_mass_ne_zero E hE x hx i)
  · intro i
    exact constituentPrimePrior_historyFrequencyUnits _ width E hE hF x hx S hS [] h i

theorem terminalRootIntegrand_total_norm_sq_le (k j : ℕ) (width : Role → ℕ)
    {Q F : ℕ} (E : (schedule k j).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀i,0<primeShellMass (E i))
    (χ : PrimeCharacterData (schedule k j) width Q)
    (hχ : ∀i p,p∈E i → χ i p≠1)
    (a : PrimeTranslationData (schedule k j) width Q)
    (hF : ∀i p,p∈E i → F<p.val)
    (B V : (l:ℕ) → State k (l+1) → ℤ)
    (extra : (l:ℕ) → ℤ → State k l → HistoryReconstruction.Tree l → Prop)
    (mask : (l:ℕ) → ℤ → State k l → Prop) (X Δ W : ℝ)
    (S : List Bool → Finset ℤ) (hS : ∀path f,f∈S path → f≠0 ∧ f.natAbs≤F)
    (x : (schedule k j).Constituent width → PrimeUpTo Q)
    (hx : (constituentPrimePrior (schedule k j) width E hE).mass x≠0) :
    (∑s : ↥(S []),‖terminalRootIntegrand k j width χ a B V extra mask X Δ W S x s‖^2) ≤
      ∑h : SupportedHistory S j [],‖retainedHistoryWeight k B V extra mask X Δ W j h.val.1
        (constituentSampleState (schedule k j) width x) h.val.2‖^2 := by
  by_cases hp : samplePrimeSupport (schedule k j) width x
  · simp only [terminalRootIntegrand,ite_eq_left hp]
    exact historyRootSum_total_norm_sq_le k j S [] B V extra mask X Δ W _
      (fun _ h => sampledHistoryPhase k j width χ a x h.val.1 h.val.2)
      (fun _ h => (norm_sampledHistoryPhase_of_mass_ne_zero k j width E hE χ hχ a hF S hS x hx hp h).le)
  · simp only [terminalRootIntegrand,ite_eq_right hp,norm_zero,zero_pow (by decide : 2≠0),
      Finset.sum_const_zero]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem terminalRootIntegrand_mean_norm_sq_le (k j : ℕ) (width : Role → ℕ)
    {Q F : ℕ} (E : (schedule k j).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀i,0<primeShellMass (E i))
    (χ : PrimeCharacterData (schedule k j) width Q)
    (hχ : ∀i p,p∈E i → χ i p≠1)
    (a : PrimeTranslationData (schedule k j) width Q)
    (hF : ∀i p,p∈E i → F<p.val)
    (B V : (l:ℕ) → State k (l+1) → ℤ)
    (extra : (l:ℕ) → ℤ → State k l → HistoryReconstruction.Tree l → Prop)
    (mask : (l:ℕ) → ℤ → State k l → Prop) (X Δ W : ℝ)
    (S : List Bool → Finset ℤ) (hS : ∀path f,f∈S path → f≠0 ∧ f.natAbs≤F) :
    (constituentPrimePrior (schedule k j) width E hE).mean (fun x =>
      ∑s : ↥(S []),‖terminalRootIntegrand k j width χ a B V extra mask X Δ W S x s‖^2) ≤
    (constituentPrimePrior (schedule k j) width E hE).mean (fun x =>
      ∑h : SupportedHistory S j [],‖retainedHistoryWeight k B V extra mask X Δ W j h.val.1
        (constituentSampleState (schedule k j) width x) h.val.2‖^2) := by
  apply Finset.sum_le_sum
  intro x hx
  by_cases hm : (constituentPrimePrior (schedule k j) width E hE).mass x=0
  · simp only [hm,zero_mul,le_refl]
  · exact mul_le_mul_of_nonneg_left
      (terminalRootIntegrand_total_norm_sq_le k j width E hE χ hχ a hF B V extra mask X Δ W S hS x hm)
      ((constituentPrimePrior (schedule k j) width E hE).mass_nonneg x)

end Ostmann.Characters.Template

end

end OAI
