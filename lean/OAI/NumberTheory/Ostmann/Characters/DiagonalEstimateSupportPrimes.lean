import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportTags
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceUnitSource
import OAI.NumberTheory.Ostmann.Characters.TemplateDiagonalMatching

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction Preliminaries
attribute [local instance] Classical.propDecidable

theorem copiedSample_injective_of_current {k j Q : ℕ} (width : Role → ℕ)
    (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideState k j) (P s : ℤ)
    (hs : CurrentAtomSupport k j s
      (sourceState k j P (copiedSampleState (schedule k j) j width h) y))
    (hw : copiedWithinAtomPrimeSupport (schedule k j) j width h) :
    Function.Injective (fun i => (h i).val) := by
  have hc : Pairwise (fun i t => (∏ a,(h ⟨i,a⟩).val).Coprime (∏ b,(h ⟨t,b⟩).val)) := by
    simpa only [copiedSampleState,←Nat.cast_prod,Nat.isCoprime_iff_coprime] using hs.copied_pairwise
  have hp : Pairwise (fun i t => (h i).val.Coprime (h t).val) :=
    (pairwise_coprime_sigma_iff (fun i => (h i).val)).mpr ⟨hc,hw⟩
  intro i t hit
  by_contra hne
  have he : (h t).val=1 := by simpa only [hit,Nat.coprime_self] using hp hne
  exact (primeUpTo_prime (h t)).ne_one he

namespace RetainedRow
section
variable (k j : ℕ) (hj : j < k) (width : Role → ℕ) {Q : ℕ}
    (ζ : PrimeUnitData (schedule k j) width Q)
    (χ : PrimeCharacterData (schedule k j) width Q)
    (a : PrimeTranslationData (schedule k j) width Q)
    (B V : (l:ℕ) → State k (l+1) → ℤ)
    (extra : (l:ℕ) → ℤ → State k l → HistoryReconstruction.Tree l → Prop)
    (mask : (l:ℕ) → ℤ → State k l → Prop) (X Δ W : ℝ)
    (P : ℕ+) (h : CopiedConstituent (schedule k j) j width → PrimeUpTo Q)
    (y : OutsideConstituent (schedule k j) j width → PrimeUpTo Q)
    (z : ℤ×HistoryReconstruction.Tree j)

theorem unit_term_copiedWithin
    (hf : term k j B V extra mask X Δ W P
      (copiedSampleState (schedule k j) j width h) (outsideSampleState (schedule k j) j width y)
      z (unitRetainedPhase k j hj width ζ χ a h y P z.1 z.2)≠0) :
    copiedWithinAtomPrimeSupport (schedule k j) j width h := by
  have hu : unitRetainedPhase k j hj width ζ χ a h y P z.1 z.2≠0 :=
    (mul_ne_zero_iff.mp hf).2
  have hp : sampledRetainedPhase k j hj width χ a h y P z.1 z.2≠0 :=
    (mul_ne_zero_iff.mp hu).2
  by_contra hn
  simp only [sampledRetainedPhase,hn,false_and,ite_false] at hp
  exact hp rfl

theorem unit_term_copiedSample_injective
    (hf : term k j B V extra mask X Δ W P
      (copiedSampleState (schedule k j) j width h) (outsideSampleState (schedule k j) j width y)
      z (unitRetainedPhase k j hj width ζ χ a h y P z.1 z.2)≠0) :
    Function.Injective (fun i => (h i).val) := by
  apply copiedSample_injective_of_current width h
    (outsideSampleState (schedule k j) j width y) (P:ℤ) z.1
  · exact term_current_support k j B V extra mask X Δ W P _ _ z _ hf
  · exact unit_term_copiedWithin k j hj width ζ χ a B V extra mask X Δ W P h y z hf

end
end RetainedRow
end Ostmann.Characters.Template

end

end OAI
