import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationFinite
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceSourceTransportLaws
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceFlagReplacementLaws

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation
open Construction Construction.CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairPattern HistoryPairRows HistoryPairSourceLaws HistoryPairSourceCoordinates
open HistoryPairReferenceSourceTransport HistoryPairSourceFlagReplacement
attribute [local instance] Classical.propDecidable
local instance activeSourceInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
  {outside : List ℕ} {l : ℕ}

abbrev OriginalDraw (giants : Bool → PrimeSource)
    (sources : SourceFamily) (seed : List SourceSlot) (l : ℕ)
    (p : Pattern (pairedHistoryType seed l)) :=
  ∀i,mixedCarrier giants (templateRootSources sources seed l) sources (pairedInternalOrigin seed l) p i

def originalDrawValues (giants : Bool → PrimeSource)
    (sources : SourceFamily) (seed : List SourceSlot) (l : ℕ)
    (p : Pattern (pairedHistoryType seed l)) (y : OriginalDraw giants sources seed l p) :
    TypedSourceIndex p → ℤ :=
  fun i=>mixedValue giants (templateRootSources sources seed l) sources (pairedInternalOrigin seed l) p i (y i)

def originalDrawMass (giants : Bool → PrimeSource)
    (sources : SourceFamily) (seed : List SourceSlot) (l : ℕ)
    (p : Pattern (pairedHistoryType seed l)) (y : OriginalDraw giants sources seed l p) : ℝ :=
  ∏i,mixedWeight giants (templateRootSources sources seed l) sources (pairedInternalOrigin seed l) p i (y i)

theorem originalDrawMass_nonneg (giants : Bool → PrimeSource)
    (sources : SourceFamily) (seed : List SourceSlot) (l : ℕ)
    (p : Pattern (pairedHistoryType seed l)) (y : OriginalDraw giants sources seed l p) :
    0 ≤ originalDrawMass giants sources seed l p y :=
  Finset.prod_nonneg (fun i _ => mixedWeight_nonneg giants _ sources _ p i (y i))

variable (giants : Bool → PrimeSource) (p : Pattern (pairedHistoryType seed l))
  {α : Type*} (outer : OriginalDraw giants sources seed l p → α) (active : α → Prop)
  (D E : (i : α) → active i → DecodedDraw sources seed V outside l)
  (b : (i : α) → active i → BlockDraw p ℕ)
  (hv : ∀ i hi j, (slot (D i hi).history (E i hi).history (pairedOccurrenceEquiv (D i hi) (E i hi) j)).value=
    expand p (b i hi) j)
  (hperm : ∀ i hi, (D i hi).history.root.small.Perm (E i hi).history.root.small)

def activeSourceMean (w : OriginalDraw giants sources seed l p → ℝ) : ℝ :=
  ∑ y : OriginalDraw giants sources seed l p, originalDrawMass giants sources seed l p y *
    if hy : active (outer y) then w y * family (D (outer y) hy) (E (outer y) hy)
      (originalDrawValues giants sources seed l p y ∘
        (typedSourceEquiv (D (outer y) hy) (E (outer y) hy) p (b (outer y) hy)
          (hv (outer y) hy) (hperm (outer y) hy)).symm) else 0

theorem activeSourceMean_le_canonical
    (D0 E0 : DecodedDraw sources seed V outside l) (b0 : BlockDraw p ℕ)
    (hv0 : ∀ j, (slot D0.history E0.history (pairedOccurrenceEquiv D0 E0 j)).value=expand p b0 j)
    (hperm0 : D0.history.root.small.Perm E0.history.root.small)
    (hD : ∀ i hi, (D i hi).SameFrequencies D0)
    (hE : ∀ i hi, (E i hi).SameFrequencies E0)
    (hp : ∀ i hi, SamePairPattern seed (D i hi).history (E i hi).history D0.history E0.history
      (D i hi).labels (E i hi).labels D0.labels E0.labels)
    (w : OriginalDraw giants sources seed l p → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hw : ∀ y, active (outer y) → originalDrawMass giants sources seed l p y ≠ 0 → w y ≤ A) :
    activeSourceMean giants p outer active D E b hv hperm w ≤
      A * canonicalSourceMean D0 E0 p b0 hv0 hperm0 giants (family D0 E0) := by
  unfold activeSourceMean canonicalSourceMean
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _
  change originalDrawMass giants sources seed l p y * _ ≤
    A * (originalDrawMass giants sources seed l p y * family D0 E0
      (originalDrawValues giants sources seed l p y ∘ (typedSourceEquiv D0 E0 p b0 hv0 hperm0).symm))
  by_cases hm : originalDrawMass giants sources seed l p y=0
  · simp only [hm,zero_mul,mul_zero,le_refl]
  have hμ := originalDrawMass_nonneg giants sources seed l p y
  by_cases hy : active (outer y)
  · rw [dite_eq_left hy]
    have he := family_eq_pullSample (D (outer y) hy) (E (outer y) hy) D0 E0
      (hD (outer y) hy) (hE (outer y) hy) (hp (outer y) hy)
      (originalDrawValues giants sources seed l p y ∘
        (typedSourceEquiv (D (outer y) hy) (E (outer y) hy) p (b (outer y) hy)
          (hv (outer y) hy) (hperm (outer y) hy)).symm)
    have hx := typedSourceEquiv_pullSample (D (outer y) hy) (E (outer y) hy) D0 E0
      (hp (outer y) hy) p (b (outer y) hy) b0 (hv (outer y) hy) hv0 (hperm (outer y) hy) hperm0
      (originalDrawValues giants sources seed l p y)
    rw [he,show pullSample (D (outer y) hy) (E (outer y) hy) D0 E0 (hp (outer y) hy)
      (originalDrawValues giants sources seed l p y ∘
        (typedSourceEquiv (D (outer y) hy) (E (outer y) hy) p (b (outer y) hy)
          (hv (outer y) hy) (hperm (outer y) hy)).symm)=
      originalDrawValues giants sources seed l p y ∘ (typedSourceEquiv D0 E0 p b0 hv0 hperm0).symm from hx]
    calc
      _ ≤ originalDrawMass giants sources seed l p y * (A * family D0 E0 _) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hw y hy hm) (family_nonneg D0 E0 _)) hμ
      _ = _ := by ring
  · rw [dite_eq_right hy,mul_zero]
    exact mul_nonneg hA (mul_nonneg hμ (family_nonneg D0 E0 _))

end Ostmann.Arithmetic.HistoryPairReferenceFlagExpectation

end

end OAI
