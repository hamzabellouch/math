import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationFinite

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation
open Construction Construction.CanonicalOccurrenceTransport HistoryPairPattern
open HistoryPairBulkTransport HistoryPairReferenceFlagsTransport
attribute [local instance] Classical.propDecidable

variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ} {α β : Type*} [Fintype α] [Fintype β]

def drawFixedSamples (active : α → Prop)
    (D E : (i : α) → active i → DecodedDraw sources seed V outside l)
    (D0 E0 : DecodedDraw sources seed V outside l)
    (σ : Equiv.Perm (Fin (Template.current seed l).length))
    (hroot : ∀ i hi t, coordinateSample seed (E i hi).history (E i hi).labels (.inr (.inl t))=
      coordinateSample seed (D i hi).history (D i hi).labels (.inr (.inl (σ t))))
    (hroot0 : ∀ t, coordinateSample seed E0.history E0.labels (.inr (.inl t))=
      coordinateSample seed D0.history D0.labels (.inr (.inl (σ t))))
    (hpattern : ∀ i hi, pairedDrawPattern sources seed V l (D i hi).choices (E i hi).choices=
      pairedDrawPattern sources seed V l D0.choices E0.choices)
    (x : (i : α) → (hi : active i) → β → PairKey (D i hi).history (E i hi).history → ℤ)
    (inactive : α → β → PairKey D0.history E0.history → ℤ) :
    α → β → PairKey D0.history E0.history → ℤ :=
  fixedSamples active D E D0 E0
    (fun i hi => samePairPattern_of_drawPattern (D i hi) (E i hi) D0 E0 σ
      (hroot i hi) hroot0 (hpattern i hi)) x inactive

theorem activeMean_le_fixed_draw (μ : α → ℝ) (ν w : α → β → ℝ) (active : α → Prop)
    (D E : (i : α) → active i → DecodedDraw sources seed V outside l)
    (D0 E0 : DecodedDraw sources seed V outside l)
    (hD : ∀ i hi, (D i hi).SameFrequencies D0)
    (hE : ∀ i hi, (E i hi).SameFrequencies E0)
    (σ : Equiv.Perm (Fin (Template.current seed l).length))
    (hroot : ∀ i hi t, coordinateSample seed (E i hi).history (E i hi).labels (.inr (.inl t))=
      coordinateSample seed (D i hi).history (D i hi).labels (.inr (.inl (σ t))))
    (hroot0 : ∀ t, coordinateSample seed E0.history E0.labels (.inr (.inl t))=
      coordinateSample seed D0.history D0.labels (.inr (.inl (σ t))))
    (hpattern : ∀ i hi, pairedDrawPattern sources seed V l (D i hi).choices (E i hi).choices=
      pairedDrawPattern sources seed V l D0.choices E0.choices)
    (x : (i : α) → (hi : active i) → β → PairKey (D i hi).history (E i hi).history → ℤ)
    (inactive : α → β → PairKey D0.history E0.history → ℤ)
    (A : ℝ) (hA : 0 ≤ A) (hμ : ∀ i, 0 ≤ μ i) (hν : ∀ i j, 0 ≤ ν i j)
    (hw : ∀ i, active i → μ i ≠ 0 → ∀ j, ν i j ≠ 0 → w i j ≤ A) :
    activeMean μ ν w active D E x ≤
      A * ∑ i, μ i * ∑ j, ν i j * family D0 E0
        (drawFixedSamples active D E D0 E0 σ hroot hroot0 hpattern x inactive i j) :=
  activeMean_le_fixed μ ν w active D E D0 E0 hD hE
    (fun i hi => samePairPattern_of_drawPattern (D i hi) (E i hi) D0 E0 σ
      (hroot i hi) hroot0 (hpattern i hi)) x inactive A hA hμ hν hw

end Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation

end

end OAI
