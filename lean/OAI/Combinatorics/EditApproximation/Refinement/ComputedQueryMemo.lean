import OAI.Combinatorics.EditApproximation.Queries.QueryFamilyNormalize
import OAI.Combinatorics.EditApproximation.Refinement.ComputedSeedWords
import OAI.Combinatorics.EditApproximation.Refinement.ComputedKernelWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

private theorem computed_small_word_pos (N : ℕ) : 0 < bitWordValue (inputSmallLog N).bits := by
  rw [bitWordValue_bits]
  exact Nat.two_pow_pos _

/-- The same materialized binary constants are shared by all requests of a pass. -/




theorem computedQueryBase_value (N : ℕ) :
    bitWordValue (computedQueryBase N) = inputSmallLog N ^ 10 + 1 := by
  simp only [computedQueryBase, refinementBaseWithWork_value, bitWordValue_bits]

theorem computedQueryBase_pos (N : ℕ) : 0 < bitWordValue (computedQueryBase N) := by
  rw [computedQueryBase_value]
  omega

attribute [local instance] OAI.EditApproximation.queryArityNeZero

attribute [local instance] OAI.EditApproximation.queryRoundsNeZero

/-- Coarse words here are the stored outputs of the separately charged coarse
initializer. The adaptive mixed memo consumes them on demand. -/
def computedQueryMemoRaw (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) (key : ComputedFamilyMemoKey source target N) :=
  queryFamilyMemoRaw source target N (integerParameters N).P (inputSmallLog N)
    (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
    (heightExponent N / 20) (smallLogExponent N) (computedParameterP_pos N) rfl rfl
    (fun pass => (scheduledSeedWordWithWork N pass).1)
    (fun pass => (computedQueryParameters N pass).factor)
    (computedQueryParameters N 0).tau (computedQueryParameters N 0).eta
    (computedQueryParameters N 0).kappa (computedQueryParameters N 0).delta
    (scheduledSeedMultiplier N) occurrence symbolBits positionBits
    (fun entry => (BinaryFraction.nat (clampedSeedNat input.1 entry), 0)) input.2 key

def computedQueryMemoNormalized (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) :
    (key : ComputedFamilyMemoKey source target N) → BitQuery
      {child : ComputedFamilyMemoKey source target N //
        SourceRanked.rank ChargedPhysicalRequest.rank child < SourceRanked.rank ChargedPhysicalRequest.rank key}
      BinaryFraction :=
  rankedNormalizeBody (SourceRanked.rank ChargedPhysicalRequest.rank)
    (computedQueryMemoRaw source target N occurrence symbolBits positionBits input)
    (computedQueryBase N) (computedQueryBase_pos N)
    (queryFamilyMemoRemaining target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80))

end EditApproximation

end OAI
