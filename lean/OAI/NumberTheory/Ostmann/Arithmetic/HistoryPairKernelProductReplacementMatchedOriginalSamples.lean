import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairKernelProductReplacementOriginalSamples
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationMatchedReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationSource
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceSourceTransportMatched
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsSupportMatched
import OAI.NumberTheory.Ostmann.Construction.SourceAssignmentSupport

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairKernelProductReplacement
open Construction CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairPattern HistoryPairSourceLaws HistoryPairKernelReplacement HistoryPairReferenceFlagExpectation
open HistoryPairReferenceSourceTransport HistoryPairRows HistoryPairRepresentatives
open HistoryPairRepresentativeVariables
open HistoryCompensationRepresentativePatterns HistorySymbolicEncoding
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
    {outside : List ℕ} {l : ℕ} {p : Pattern (pairedHistoryType seed l)}

def matchedReferenceSample (R : MatchedBlockReference sources seed V outside l p)
    (giants : Bool → PrimeSource) (y : OriginalDraw giants sources seed l p) :
    PairKey R.left.history R.right.history → ℤ :=
  originalDrawValues giants sources seed l p y ∘
    (typedSourceEquivMatched R.left R.right p R.natDraw R.slot_values R.root_matching).symm

def RightRootSupported (R : MatchedBlockReference sources seed V outside l p)
    (giants : Bool → PrimeSource) (y : OriginalDraw giants sources seed l p) : Prop :=
  ∀ i : Fin R.right.history.root.small.length,
    PositiveSourceValue (sources (R.right.history.root.small.get i).origin)
      (matchedReferenceSample R giants y (rightMap R.left.history R.right.history (.inr (.inl i))))

def rightRootSupportIndicator (R : MatchedBlockReference sources seed V outside l p)
    (giants : Bool → PrimeSource) (y : OriginalDraw giants sources seed l p) : ℝ := by
  classical
  exact if RightRootSupported R giants y then 1 else 0

theorem rightRootSupportIndicator_bounds (R : MatchedBlockReference sources seed V outside l p)
    (giants : Bool → PrimeSource) (y : OriginalDraw giants sources seed l p) :
    0 ≤ rightRootSupportIndicator R giants y ∧ rightRootSupportIndicator R giants y ≤ 1 := by
  classical
  unfold rightRootSupportIndicator
  split_ifs <;> norm_num

theorem rightRootSupportIndicator_ne_zero_iff (R : MatchedBlockReference sources seed V outside l p)
    (giants : Bool → PrimeSource) (y : OriginalDraw giants sources seed l p) :
    rightRootSupportIndicator R giants y ≠ 0 ↔ RightRootSupported R giants y := by
  classical
  unfold rightRootSupportIndicator
  split_ifs <;> simp_all

theorem rightRootSupported_of_assignment (R : MatchedBlockReference sources seed V outside l p)
    (giants : Bool → PrimeSource) (y : OriginalDraw giants sources seed l p)
    (z : SourceAssignment sources (Template.current seed l))
    (hz : (assignmentPrior sources (Template.current seed l)).mass z ≠ 0)
    (hvalues : ∀ i, matchedReferenceSample R giants y
      (rightMap R.left.history R.right.history (.inr (.inl (rootPosition R.right i)))) =
      ((z i).val : ℤ)) : RightRootSupported R giants y := by
  intro j
  obtain ⟨i,rfl⟩ := (rootPosition R.right).surjective j
  rw [rootPosition_source R.right i,hvalues i]
  exact ⟨z i,rfl,assignmentPrior_component_mass_ne_zero sources _ z hz i⟩

theorem matched_originalDrawMass_smallSourceSamples (giants : Bool → PrimeSource)
    (R : MatchedBlockReference sources seed V outside l p)
    (y : OriginalDraw giants sources seed l p)
    (hy : originalDrawMass giants sources seed l p y ≠ 0)
    (hright : RightRootSupported R giants y) :
    SmallSourceSamples sources R.left.history R.right.history
      (originalDrawValues giants sources seed l p y ∘
        (typedSourceEquivMatched R.left R.right p R.natDraw R.slot_values R.root_matching).symm) := by
  apply smallSourceSamples_of_both_roots_occurrences sources R.left.history R.right.history
  · intro j
    obtain ⟨i,rfl⟩ := (rootPosition R.left).surjective j
    rw [←typedSourceEquivMatched_root R.left R.right p R.natDraw R.slot_values R.root_matching i,
      Function.comp_apply, Equiv.symm_apply_apply, rootPosition_source R.left i]
    exact ⟨y (.inr (.inl i)), rfl,
      originalDrawMass_coordinate_ne_zero giants y hy (.inr (.inl i))⟩
  · exact hright
  · intro o
    obtain ⟨i,rfl⟩ := (pairedOccurrenceEquiv R.left R.right).surjective o
    have ho : (slot R.left.history R.right.history (pairedOccurrenceEquiv R.left R.right i)).origin =
        pairedInternalOrigin seed l i :=
      pairedInternalEquiv_origin seed R.left.history R.right.history R.left.labels R.right.labels i
    have hk : typedSourceEquivMatched R.left R.right p R.natDraw R.slot_values R.root_matching
        (.inr (.inr (CompensationEqualityPatterns.label p i))) =
        representativeMap R.left.history R.right.history
          (HistoryPairRepresentatives.label R.left.history R.right.history
            (pairedOccurrenceEquiv R.left R.right i)) := by
      rw [typedSourceEquivMatched_block,
        ←typedBlockEquiv_label R.left R.right p R.natDraw R.slot_values i,
        Equiv.symm_apply_apply]
    rw [ho, ←hk, Function.comp_apply, Equiv.symm_apply_apply]
    exact positiveSourceValue_of_sourceWeight sources (pairedInternalOrigin seed l) i
      (y (.inr (.inr (CompensationEqualityPatterns.label p i))))
      (biasedBlockWeight_source_nonzero sources (pairedInternalOrigin seed l) p
        (CompensationEqualityPatterns.label p i) _
        (originalDrawMass_coordinate_ne_zero giants y hy
          (.inr (.inr (CompensationEqualityPatterns.label p i)))) ⟨i,rfl⟩)

end Ostmann.Arithmetic.HistoryPairKernelProductReplacement

end

end OAI
