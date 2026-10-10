import OAI.NumberTheory.TwoPoint.Bounds.PrimeWordEncoding
import OAI.NumberTheory.TwoPoint.Bounds.SplitBadWordSum

namespace OAI

/-! Encoding the actual prohibited numerical words in the reciprocal catalog. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

namespace PrimeWordEncoding

variable {R T : ℕ} {P Q : Finset ℕ}

def Prohibited (e : PrimeWordEncoding R T P Q) (h s J : ℕ)
    (supply : ℕ → ℕ → Prop) : Prop :=
  e.2.1.KindConsistent ∧ e.2.1.RowInjective ∧
  Function.Injective (fun z => (e.2.2.1 z).val) ∧
  ForwardProhibited h s supply e.decode ∧
  (∀ a ∈ e.decode, Squarefree a.tuple) ∧
  (∀ a ∈ e.decode, a.tuple.primeFactors.card = J) ∧
  (∀ p j, TuplePrimeAt e.decode p j → ¬p ∣ h ∧ ∀ a ∈ e.decode, ¬p ∣ a.padding)

theorem covers_prohibited (w : Fin R → SignedStep)
    (hT : Fintype.card (ActualPrimeSlot w) ≤ T)
    (ht : ∀ i, Squarefree (w i).tuple) (hq : ∀ i, Squarefree (w i).padding)
    (hP : ∀ i, (w i).tuple.primeFactors ⊆ P)
    (hQ : ∀ i, (w i).padding.primeFactors ⊆ Q)
    (hd : ∀ i j, Disjoint (w i).tuple.primeFactors (w j).padding.primeFactors)
    (h s J : ℕ) (supply : ℕ → ℕ → Prop)
    (hw : ForwardProhibited h s supply (List.ofFn w))
    (hJ : ∀ i, (w i).tuple.primeFactors.card = J)
    (hsupport : ∀ p j, TuplePrimeAt (List.ofFn w) p j →
      ¬p ∣ h ∧ ∀ a ∈ List.ofFn w, ¬p ∣ a.padding) :
    ∃ e : PrimeWordEncoding R T P Q, e.Prohibited h s J supply ∧
      e.decode = List.ofFn w ∧
      e.weight = ∏ p ∈ wordDivisorPrimeSupport (List.ofFn w), (p : ℝ)⁻¹ := by
  obtain ⟨e, he, hc, hi, hinj, hweight⟩ := covers w hT ht hq hP hQ hd
  refine ⟨e, ⟨hc, hi, hinj, ?_⟩, he, hweight⟩
  rw [he]
  refine ⟨hw, ?_, ?_, hsupport⟩
  · intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact ht i
  · intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hJ i

end PrimeWordEncoding

end TwoPointCorrelations

end OAI
