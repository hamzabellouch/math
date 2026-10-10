import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationSourceActual

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation
open Construction Construction.CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairPattern HistoryPairRows HistoryPairSourceLaws HistoryPairSourceCoordinates
open HistoryPairReferenceSourceTransport HistoryPairReferenceFlagsTransport HistoryPairBulkTransport
attribute [local instance] Classical.propDecidable
local instance activeSourceSelectionInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ}

variable (giants : Bool → PrimeSource) (p : Pattern (pairedHistoryType seed l))
  {α : Type*} (outer : OriginalDraw giants sources seed l p → α) (active : α → Prop)
  (D E : (i : α) → active i → DecodedDraw sources seed V outside l)
  (b : (i : α) → active i → BlockDraw p ℕ)
  (hv : ∀ i hi j, (slot (D i hi).history (E i hi).history (pairedOccurrenceEquiv (D i hi) (E i hi) j)).value=
    expand p (b i hi) j)
  (hperm : ∀ i hi, (D i hi).history.root.small.Perm (E i hi).history.root.small)

theorem activeSourceMean_zero_of_no_reference
    (w : OriginalDraw giants sources seed l p → ℝ)
    (hn : ¬∃y,originalDrawMass giants sources seed l p y ≠ 0 ∧ active (outer y)) :
    activeSourceMean giants p outer active D E b hv hperm w=0 := by
  apply Finset.sum_eq_zero
  intro y _
  by_cases hm : originalDrawMass giants sources seed l p y=0
  · simp only [hm,zero_mul]
  · have hy : ¬active (outer y) := fun hy => hn ⟨y,hm,hy⟩
    simp only [dite_eq_right hy,mul_zero]

theorem activeSourceMean_zero_or_reference
    (hD : ∀ i hi j hj, (D i hi).SameFrequencies (D j hj))
    (hE : ∀ i hi j hj, (E i hi).SameFrequencies (E j hj))
    (σ : Equiv.Perm (Fin (Template.current seed l).length))
    (hroot : ∀ i hi t, coordinateSample seed (E i hi).history (E i hi).labels (.inr (.inl t))=
      coordinateSample seed (D i hi).history (D i hi).labels (.inr (.inl (σ t))))
    (hpattern : ∀ i hi j hj, pairedDrawPattern sources seed V l (D i hi).choices (E i hi).choices=
      pairedDrawPattern sources seed V l (D j hj).choices (E j hj).choices)
    (w : OriginalDraw giants sources seed l p → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hw : ∀ y, active (outer y) → originalDrawMass giants sources seed l p y ≠ 0 → w y ≤ A) :
    activeSourceMean giants p outer active D E b hv hperm w=0 ∨
      ∃(y : OriginalDraw giants sources seed l p),originalDrawMass giants sources seed l p y ≠ 0 ∧
        ∃hy : active (outer y),activeSourceMean giants p outer active D E b hv hperm w ≤
          A * canonicalSourceMean (D (outer y) hy) (E (outer y) hy) p (b (outer y) hy)
            (hv (outer y) hy) (hperm (outer y) hy) giants (family (D (outer y) hy) (E (outer y) hy)) := by
  by_cases he : ∃y,originalDrawMass giants sources seed l p y ≠ 0 ∧ active (outer y)
  · obtain ⟨y,hm,hy⟩ := he
    refine Or.inr ⟨y,hm,hy,?_⟩
    exact activeSourceMean_le_canonical_draw giants p outer active D E b hv hperm
      (D (outer y) hy) (E (outer y) hy) (b (outer y) hy) (hv (outer y) hy) (hperm (outer y) hy)
      (fun i hi => hD i hi (outer y) hy) (fun i hi => hE i hi (outer y) hy)
      σ hroot (hroot (outer y) hy) (fun i hi => hpattern i hi (outer y) hy) w A hA hw
  · exact Or.inl (activeSourceMean_zero_of_no_reference giants p outer active D E b hv hperm w he)

end Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation

end

end OAI
