import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationSource

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation
open Construction Construction.CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairPattern HistoryPairRows HistoryPairSourceLaws HistoryPairSourceCoordinates
open HistoryPairReferenceSourceTransport HistoryPairReferenceFlagsTransport HistoryPairBulkTransport
attribute [local instance] Classical.propDecidable
local instance activeSourceActualInternalDecidable (seed : List SourceSlot) (l : ℕ) :
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

theorem activeSourceMean_le_canonical_draw
    (D0 E0 : DecodedDraw sources seed V outside l) (b0 : BlockDraw p ℕ)
    (hv0 : ∀ j, (slot D0.history E0.history (pairedOccurrenceEquiv D0 E0 j)).value=expand p b0 j)
    (hperm0 : D0.history.root.small.Perm E0.history.root.small)
    (hD : ∀ i hi, (D i hi).SameFrequencies D0)
    (hE : ∀ i hi, (E i hi).SameFrequencies E0)
    (σ : Equiv.Perm (Fin (Template.current seed l).length))
    (hroot : ∀ i hi t, coordinateSample seed (E i hi).history (E i hi).labels (.inr (.inl t))=
      coordinateSample seed (D i hi).history (D i hi).labels (.inr (.inl (σ t))))
    (hroot0 : ∀ t, coordinateSample seed E0.history E0.labels (.inr (.inl t))=
      coordinateSample seed D0.history D0.labels (.inr (.inl (σ t))))
    (hpattern : ∀ i hi, pairedDrawPattern sources seed V l (D i hi).choices (E i hi).choices=
      pairedDrawPattern sources seed V l D0.choices E0.choices)
    (w : OriginalDraw giants sources seed l p → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hw : ∀ y, active (outer y) → originalDrawMass giants sources seed l p y ≠ 0 → w y ≤ A) :
    activeSourceMean giants p outer active D E b hv hperm w ≤
      A * canonicalSourceMean D0 E0 p b0 hv0 hperm0 giants (family D0 E0) :=
  activeSourceMean_le_canonical giants p outer active D E b hv hperm D0 E0 b0 hv0 hperm0 hD hE
    (fun i hi => samePairPattern_of_drawPattern (D i hi) (E i hi) D0 E0 σ
      (hroot i hi) hroot0 (hpattern i hi)) w A hA hw

end Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation

end

end OAI
