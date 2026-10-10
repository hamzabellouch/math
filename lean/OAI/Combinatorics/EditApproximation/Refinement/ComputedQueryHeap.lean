import OAI.Combinatorics.EditApproximation.Queries.QueryFamilyMemoSpace
import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryMemo

namespace OAI

namespace EditApproximation
attribute [local instance] queryArityNeZero queryRoundsNeZero

/-- Coarse words are borrowed from the separately allocated initializer.
Every local buffer, guarded source read and final normalization is annotated. -/
def computedQueryMemoRawHeap (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) (key : ComputedFamilyMemoKey source target N) :
    BitQuery.Heap (computedQueryMemoRaw source target N occurrence symbolBits positionBits input key) :=
  queryFamilyMemoRawHeap source target N (integerParameters N).P (inputSmallLog N)
    (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
    (heightExponent N / 20) (smallLogExponent N) (computedParameterP_pos N) rfl rfl
    (fun pass => (scheduledSeedWordWithWork N pass).1)
    (fun pass => (computedQueryParameters N pass).factor)
    (computedQueryParameters N 0).tau (computedQueryParameters N 0).eta
    (computedQueryParameters N 0).kappa (computedQueryParameters N 0).delta
    (scheduledSeedMultiplier N) occurrence symbolBits positionBits
    (fun entry => (BinaryFraction.nat (clampedSeedNat input.1 entry), 0))
    (fun _ => 0) (fun _ => le_rfl) input.2 key

def computedQueryMemoHeap (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) (key : ComputedFamilyMemoKey source target N) :
    BitQuery.Heap (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input key) :=
  (computedQueryMemoRawHeap source target N occurrence symbolBits positionBits input key).normalize
    (computedQueryBase N) (computedQueryBase_pos N)
    (queryFamilyMemoRemaining target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80) key)

end EditApproximation

end OAI
