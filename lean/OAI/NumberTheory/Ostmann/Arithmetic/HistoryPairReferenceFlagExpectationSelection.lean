import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationActual

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation
open Construction Construction.CanonicalOccurrenceTransport HistoryPairPattern HistoryPairBulkTransport
attribute [local instance] Classical.propDecidable

variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ} {α β : Type*} [Fintype α] [Fintype β]

theorem zero_or_fixed_draw_reference (μ : α → ℝ) (ν w : α → β → ℝ) (active : α → Prop)
    (D E : (i : α) → active i → DecodedDraw sources seed V outside l)
    (hD : ∀ i hi j hj, (D i hi).SameFrequencies (D j hj))
    (hE : ∀ i hi j hj, (E i hi).SameFrequencies (E j hj))
    (σ : Equiv.Perm (Fin (Template.current seed l).length))
    (hroot : ∀ i hi t, coordinateSample seed (E i hi).history (E i hi).labels (.inr (.inl t))=
      coordinateSample seed (D i hi).history (D i hi).labels (.inr (.inl (σ t))))
    (hpattern : ∀ i hi j hj, pairedDrawPattern sources seed V l (D i hi).choices (E i hi).choices=
      pairedDrawPattern sources seed V l (D j hj).choices (E j hj).choices)
    (x : (i : α) → (hi : active i) → β → PairKey (D i hi).history (E i hi).history → ℤ)
    (inactive : (r : α) → (hr : active r) → α → β → PairKey (D r hr).history (E r hr).history → ℤ)
    (A : ℝ) (hA : 0 ≤ A) (hμ : ∀ i, 0 ≤ μ i) (hν : ∀ i j, 0 ≤ ν i j)
    (hw : ∀ i, active i → μ i ≠ 0 → ∀ j, ν i j ≠ 0 → w i j ≤ A) :
    activeMean μ ν w active D E x=0 ∨
      ∃ (r : α) (hr : active r), activeMean μ ν w active D E x ≤
        A * ∑ i, μ i * ∑ j, ν i j * family (D r hr) (E r hr)
          (drawFixedSamples active D E (D r hr) (E r hr) σ hroot (hroot r hr)
            (fun i hi => hpattern i hi r hr) x (inactive r hr) i j) := by
  by_cases he : ∃ i, active i
  · obtain ⟨r,hr⟩ := he
    exact Or.inr ⟨r,hr,activeMean_le_fixed_draw μ ν w active D E (D r hr) (E r hr)
      (fun i hi => hD i hi r hr) (fun i hi => hE i hi r hr)
      σ hroot (hroot r hr) (fun i hi => hpattern i hi r hr) x (inactive r hr) A hA hμ hν hw⟩
  · exact Or.inl (activeMean_zero_of_inactive μ ν w active D E x (fun i hi => he ⟨i,hi⟩))

end Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation

end

end OAI
