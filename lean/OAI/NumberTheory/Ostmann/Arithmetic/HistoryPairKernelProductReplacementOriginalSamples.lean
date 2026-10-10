import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationSelectedReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairReferenceFlagExpectationSource
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsSupportTransport

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairKernelProductReplacement
open Construction CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryPairKernelReplacement HistoryPairReferenceFlagExpectation
open HistoryPairReferenceSourceTransport HistoryPairRows HistoryPairRepresentatives
open HistoryPairRepresentativeVariables
open HistoryCompensationRepresentativePatterns HistorySymbolicEncoding
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _
variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
    {outside : List ℕ} {l : ℕ} {p : Pattern (pairedHistoryType seed l)}

theorem originalDrawMass_coordinate_ne_zero (giants : Bool → PrimeSource)
    (y : OriginalDraw giants sources seed l p)
    (hy : originalDrawMass giants sources seed l p y ≠ 0) (i : TypedSourceIndex p) :
    mixedWeight giants (templateRootSources sources seed l) sources
      (pairedInternalOrigin seed l) p i (y i) ≠ 0 := by
  intro hi
  apply hy
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

theorem originalDrawMass_smallSourceSamples (giants : Bool → PrimeSource)
    (R : BlockReference sources seed V outside l p)
    (y : OriginalDraw giants sources seed l p)
    (hy : originalDrawMass giants sources seed l p y ≠ 0) :
    SmallSourceSamples sources R.left.history R.right.history
      (originalDrawValues giants sources seed l p y ∘
        (typedSourceEquiv R.left R.right p R.natDraw R.slot_values R.root_perm).symm) := by
  apply smallSourceSamples_of_roots_occurrences sources R.left.history R.right.history R.root_perm
  · intro j
    obtain ⟨i,rfl⟩ := (rootPosition R.left).surjective j
    rw [←typedSourceEquiv_root R.left R.right p R.natDraw R.slot_values R.root_perm i,
      Function.comp_apply, Equiv.symm_apply_apply, rootPosition_source R.left i]
    exact ⟨y (.inr (.inl i)), rfl,
      originalDrawMass_coordinate_ne_zero giants y hy (.inr (.inl i))⟩
  · intro o
    obtain ⟨i,rfl⟩ := (pairedOccurrenceEquiv R.left R.right).surjective o
    have ho : (slot R.left.history R.right.history (pairedOccurrenceEquiv R.left R.right i)).origin =
        pairedInternalOrigin seed l i :=
      pairedInternalEquiv_origin seed R.left.history R.right.history R.left.labels R.right.labels i
    have hk : typedSourceEquiv R.left R.right p R.natDraw R.slot_values R.root_perm
        (.inr (.inr (CompensationEqualityPatterns.label p i))) =
        representativeMap R.left.history R.right.history
          (HistoryPairRepresentatives.label R.left.history R.right.history
            (pairedOccurrenceEquiv R.left R.right i)) := by
      rw [typedSourceEquiv_block,
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
