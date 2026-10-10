import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceAmplitude
import OAI.NumberTheory.Ostmann.Characters.TemplateHistoryRootNorm

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

def terminalRootIntegrand (k j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (B V : (l:ℕ) → State k (l+1) → ℤ)
    (extra : (l:ℕ) → ℤ → State k l → HistoryReconstruction.Tree l → Prop)
    (mask : (l:ℕ) → ℤ → State k l → Prop) (X Δ W : ℝ)
    (S : List Bool → Finset ℤ)
    (x : (schedule k j).Constituent width → PrimeUpTo Q) (s : ↥(S [])) : ℂ :=
  if samplePrimeSupport (schedule k j) width x then
    historyRootSum k j S [] B V extra mask X Δ W s.val
      (constituentSampleState (schedule k j) width x)
      (fun h => sampledHistoryPhase k j width χ a x h.val.1 h.val.2)
  else 0

theorem sum_terminalRootIntegrand (k j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (B V : (l:ℕ) → State k (l+1) → ℤ)
    (extra : (l:ℕ) → ℤ → State k l → HistoryReconstruction.Tree l → Prop)
    (mask : (l:ℕ) → ℤ → State k l → Prop) (X Δ W : ℝ)
    (S : List Bool → Finset ℤ)
    (x : (schedule k j).Constituent width → PrimeUpTo Q) :
    (∑s : ↥(S []), terminalRootIntegrand k j width χ a B V extra mask X Δ W S x s) =
      amplitudeIntegrand k j width χ a B V extra mask X Δ W S x := by
  by_cases hx : samplePrimeSupport (schedule k j) width x
  · simp only [terminalRootIntegrand,amplitudeIntegrand,ite_eq_left hx,historyRootSum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h hh
    have hs : h.val.1 ∈ S [] :=
      mem_labels_range S h.property (root_mem_labels j [] h.val.1 h.val.2)
    let s : ↥(S []) := ⟨h.val.1,hs⟩
    rw [Finset.sum_eq_single s]
    · simp [s]
    · intro s' hs' hne
      apply ite_eq_right
      intro he
      exact hne (Subtype.ext he.symm)
    · simp
  · simp only [terminalRootIntegrand,amplitudeIntegrand,ite_eq_right hx,Finset.sum_const_zero]

theorem actualAmplitude_eq_terminalRootMean (k j : ℕ) (width : Role → ℕ) {Q : ℕ}
    (E : (schedule k j).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀i,0<primeShellMass (E i))
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (B V : (l:ℕ) → State k (l+1) → ℤ)
    (extra : (l:ℕ) → ℤ → State k l → HistoryReconstruction.Tree l → Prop)
    (mask : (l:ℕ) → ℤ → State k l → Prop) (X Δ W : ℝ)
    (S : List Bool → Finset ℤ) :
    actualAmplitude k j width E hE χ a B V extra mask X Δ W S =
      (constituentPrimePrior (schedule k j) width E hE).cmean (fun x =>
        ∑s : ↥(S []), terminalRootIntegrand k j width χ a B V extra mask X Δ W S x s) := by
  simp only [sum_terminalRootIntegrand,actualAmplitude]

end Ostmann.Characters.Template

end

end OAI
