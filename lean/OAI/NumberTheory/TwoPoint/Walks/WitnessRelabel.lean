import OAI.NumberTheory.TwoPoint.Bounds.NumericalWitnessEvent

namespace OAI

/-! Restrict the numerical witness event to the observed tuple-prime labels. -/

namespace TwoPointCorrelations

open scoped Classical

theorem NumericalWitnessEvent.relabel {n : ℕ} {ι κ : Type*}
    {main : List SignedStep} {word : Fin n → List SignedStep}
    {p : ι → ℕ} {h s J : ℕ} {supply : ℕ → ℕ → Prop}
    (he : NumericalWitnessEvent main word p h s J supply)
    (q : κ → ℕ) (hq : Function.Injective q) (hprime : ∀ j, (q j).Prime)
    (hcover : ∀ i r, r ∈ wordPrimeSupport (word i) → ∃ j, q j = r) :
    NumericalWitnessEvent main word q h s J supply := by
  obtain ⟨mark, attachment, position, horder, hbound, _hp, _hprime,
    hminimal, hsq, hcard, hsupport, hmark, hprivate, hmain, origin, hpositive⟩ := he
  have hex (i : Fin n) : ∃ j, q j = p (mark i) := hcover i _ (hmark i)
  choose mark' hmark' using hex
  refine ⟨mark', attachment, position, horder, hbound, hq, hprime,
    hminimal, hsq, hcard, hsupport, ?_, ?_, ?_, origin, hpositive⟩
  · intro i
    rw [hmark' i]
    exact hmark i
  · intro i j hji
    rw [hmark' i]
    exact hprivate i j hji
  · intro i v hv
    rw [hmark' i] at hv
    exact hmain i v hv

end TwoPointCorrelations

end OAI
