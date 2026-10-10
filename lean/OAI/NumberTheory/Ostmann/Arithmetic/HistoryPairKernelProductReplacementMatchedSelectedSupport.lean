import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairKernelProductReplacementMatchedRootSupport
import OAI.NumberTheory.Ostmann.Conclusion.SelectedPermutation

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairKernelProductReplacement
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairPattern HistoryPairBulkCoordinates HistoryPairSourceLaws
open HistoryPairReferenceFlagExpectation HistoryPairReferenceSourceTransport
variable {sources : SourceFamily} {seed : List SourceSlot} {V : ℕ → ℕ}
    {outside : List ℕ} {l : ℕ} {p : Pattern (pairedHistoryType seed l)}

theorem matchedRightRootIndex_eq_of_aligned
    (R : MatchedBlockReference sources seed V outside l p)
    (π : Equiv.Perm (Fin (Template.current seed l).length))
    (halign : ∀ i, coordinateSample seed R.right.history R.right.labels (.inr (.inl i)) =
      coordinateSample seed R.left.history R.left.labels (.inr (.inl (π i)))) :
    matchedRightRootIndex R = π := by
  apply Equiv.ext
  intro i
  apply (rootPosition R.left).injective
  apply root_value_injective R.left.history R.left.supported
  dsimp only
  rw [matchedRightRootIndex_position,←R.root_matching.value]
  have hi := halign i
  change ((R.right.history.root.small.get (rootPosition R.right i)).value : ℤ) =
    ((R.left.history.root.small.get (rootPosition R.left (π i))).value : ℤ) at hi
  exact_mod_cast hi

theorem rightRootSupported_selected_permutation
    {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E)
    {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
    (R : MatchedBlockReference C.sources (Template.initial (2*(bulkSize k L/2)) k) V outside l p)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
    (halign : ∀ i, coordinateSample _ R.right.history R.right.labels (.inr (.inl i)) =
      coordinateSample _ R.left.history R.left.labels (.inr (.inl (selectedLeafPermutation C l σ i))))
    (giants : Bool → PrimeSource)
    (y : OriginalDraw giants C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
    (hy : originalDrawMass giants C.sources (Template.initial (2*(bulkSize k L/2)) k) l p y ≠ 0) :
    RightRootSupported R giants y := by
  apply rightRootSupported_of_source_laws R giants y hy
  intro i
  rw [matchedRightRootIndex_eq_of_aligned R _ halign]
  exact selectedLeafPermutation_source C l σ i

end Ostmann.Arithmetic.HistoryPairKernelProductReplacement

end

end OAI
