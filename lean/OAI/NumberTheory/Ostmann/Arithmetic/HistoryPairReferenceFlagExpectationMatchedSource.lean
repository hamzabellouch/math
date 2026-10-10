import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationSource
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceSourceTransportMatchedLaws

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation
open Construction Construction.CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairPattern HistoryPairRows HistoryPairSourceLaws HistoryPairSourceCoordinates
open HistoryPairReferenceSourceTransport HistoryPairSourceFlagReplacement HistoryPairBulkCoordinates
attribute [local instance] Classical.propDecidable
local instance activeMatchedSourceInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ}

variable (giants : Bool → PrimeSource) (p : Pattern (pairedHistoryType seed l))
  {α : Type*} (outer : OriginalDraw giants sources seed l p → α) (active : α → Prop)
  (D E : (i : α) → active i → DecodedDraw sources seed V outside l)
  (b : (i : α) → active i → BlockDraw p ℕ)
  (hv : ∀ i hi j, (slot (D i hi).history (E i hi).history (pairedOccurrenceEquiv (D i hi) (E i hi) j)).value=
    expand p (b i hi) j)
  (e : ∀ i hi, RootMatching (D i hi).history (E i hi).history)

def activeSourceMeanMatched (w : OriginalDraw giants sources seed l p → ℝ) : ℝ :=
  ∑ y : OriginalDraw giants sources seed l p, originalDrawMass giants sources seed l p y *
    if hy : active (outer y) then w y * family (D (outer y) hy) (E (outer y) hy)
      (originalDrawValues giants sources seed l p y ∘
        (typedSourceEquivMatched (D (outer y) hy) (E (outer y) hy) p (b (outer y) hy)
          (hv (outer y) hy) (e (outer y) hy)).symm) else 0

theorem activeSourceMeanMatched_le_canonical
    (D0 E0 : DecodedDraw sources seed V outside l) (b0 : BlockDraw p ℕ)
    (hv0 : ∀ j, (slot D0.history E0.history (pairedOccurrenceEquiv D0 E0 j)).value=expand p b0 j)
    (e0 : RootMatching D0.history E0.history)
    (hD : ∀ i hi, (D i hi).SameFrequencies D0)
    (hE : ∀ i hi, (E i hi).SameFrequencies E0)
    (hp : ∀ i hi, SamePairPattern seed (D i hi).history (E i hi).history D0.history E0.history
      (D i hi).labels (E i hi).labels D0.labels E0.labels)
    (w : OriginalDraw giants sources seed l p → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hw : ∀ y, active (outer y) → originalDrawMass giants sources seed l p y ≠ 0 → w y ≤ A) :
    activeSourceMeanMatched giants p outer active D E b hv e w ≤
      A * canonicalSourceMeanMatched D0 E0 p b0 hv0 e0 giants (family D0 E0) := by
  unfold activeSourceMeanMatched canonicalSourceMeanMatched
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _
  change originalDrawMass giants sources seed l p y * _ ≤
    A * (originalDrawMass giants sources seed l p y * family D0 E0
      (originalDrawValues giants sources seed l p y ∘ (typedSourceEquivMatched D0 E0 p b0 hv0 e0).symm))
  by_cases hm : originalDrawMass giants sources seed l p y=0
  · simp only [hm,zero_mul,mul_zero,le_refl]
  have hμ := originalDrawMass_nonneg giants sources seed l p y
  by_cases hy : active (outer y)
  · rw [dite_eq_left hy]
    have he := family_eq_pullSample (D (outer y) hy) (E (outer y) hy) D0 E0
      (hD (outer y) hy) (hE (outer y) hy) (hp (outer y) hy)
      (originalDrawValues giants sources seed l p y ∘
        (typedSourceEquivMatched (D (outer y) hy) (E (outer y) hy) p (b (outer y) hy)
          (hv (outer y) hy) (e (outer y) hy)).symm)
    have hx := typedSourceEquivMatched_pullSample (D (outer y) hy) (E (outer y) hy) D0 E0
      (hp (outer y) hy) p (b (outer y) hy) b0 (hv (outer y) hy) hv0 (e (outer y) hy) e0
      (originalDrawValues giants sources seed l p y)
    rw [he,show pullSample (D (outer y) hy) (E (outer y) hy) D0 E0 (hp (outer y) hy)
      (originalDrawValues giants sources seed l p y ∘
        (typedSourceEquivMatched (D (outer y) hy) (E (outer y) hy) p (b (outer y) hy)
          (hv (outer y) hy) (e (outer y) hy)).symm)=
      originalDrawValues giants sources seed l p y ∘ (typedSourceEquivMatched D0 E0 p b0 hv0 e0).symm from hx]
    calc
      _ ≤ originalDrawMass giants sources seed l p y * (A * family D0 E0 _) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hw y hy hm) (family_nonneg D0 E0 _)) hμ
      _ = _ := by ring
  · rw [dite_eq_right hy,mul_zero]
    exact mul_nonneg hA (mul_nonneg hμ (family_nonneg D0 E0 _))

end Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation

end

end OAI
