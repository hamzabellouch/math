import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairKernelProductReplacementMatchedOriginalSamples

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairKernelProductReplacement
open Construction CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairPattern HistoryPairBulkCoordinates HistoryPairSourceLaws
open HistoryPairReferenceFlagExpectation HistoryPairReferenceSourceTransport
variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
    {outside : List ℕ} {l : ℕ} {p : Pattern (pairedHistoryType seed l)}

def matchedRightRootIndex (R : MatchedBlockReference sources seed V outside l p) :
    Equiv.Perm (Fin (Template.current seed l).length) :=
  (rootPosition R.right).trans (R.root_matching.positions.trans (rootPosition R.left).symm)

@[simp] theorem matchedRightRootIndex_position
    (R : MatchedBlockReference sources seed V outside l p)
    (i : Fin (Template.current seed l).length) :
    rootPosition R.left (matchedRightRootIndex R i) =
      R.root_matching.positions (rootPosition R.right i) := by
  simp only [matchedRightRootIndex,Equiv.trans_apply,Equiv.apply_symm_apply]

theorem matchedReferenceSample_right_root
    (R : MatchedBlockReference sources seed V outside l p)
    (giants : Bool → PrimeSource) (y : OriginalDraw giants sources seed l p)
    (i : Fin (Template.current seed l).length) :
    matchedReferenceSample R giants y
      (rightMap R.left.history R.right.history (.inr (.inl (rootPosition R.right i)))) =
      ((y (.inr (.inl (matchedRightRootIndex R i)))).val : ℤ) := by
  rw [R.root_matching.key_eq,←matchedRightRootIndex_position R i,
    ←typedSourceEquivMatched_root R.left R.right p R.natDraw R.slot_values R.root_matching]
  simp only [matchedReferenceSample,Function.comp_apply,Equiv.symm_apply_apply]
  rfl

theorem rightRootSupported_iff_ordered
    (R : MatchedBlockReference sources seed V outside l p)
    (giants : Bool → PrimeSource) (y : OriginalDraw giants sources seed l p) :
    RightRootSupported R giants y ↔
      ∀ i, PositiveSourceValue (sources ((Template.current seed l).get i).origin)
        ((y (.inr (.inl (matchedRightRootIndex R i)))).val : ℤ) := by
  constructor
  · intro h i
    have hi := h (rootPosition R.right i)
    rwa [rootPosition_source R.right i,matchedReferenceSample_right_root] at hi
  · intro h j
    obtain ⟨i,rfl⟩ := (rootPosition R.right).surjective j
    rw [rootPosition_source R.right i,matchedReferenceSample_right_root]
    exact h i

theorem rightRootSupported_of_source_laws
    (R : MatchedBlockReference sources seed V outside l p)
    (giants : Bool → PrimeSource) (y : OriginalDraw giants sources seed l p)
    (hy : originalDrawMass giants sources seed l p y ≠ 0)
    (hlaw : ∀ i, sources ((Template.current seed l).get (matchedRightRootIndex R i)).origin =
      sources ((Template.current seed l).get i).origin) :
    RightRootSupported R giants y := by
  rw [rightRootSupported_iff_ordered]
  intro i
  rw [←hlaw i]
  exact ⟨y (.inr (.inl (matchedRightRootIndex R i))),rfl,
    originalDrawMass_coordinate_ne_zero giants y hy (.inr (.inl (matchedRightRootIndex R i)))⟩

end Ostmann.Arithmetic.HistoryPairKernelProductReplacement

end

end OAI
