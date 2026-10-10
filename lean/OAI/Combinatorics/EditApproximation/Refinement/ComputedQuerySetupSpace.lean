import OAI.Combinatorics.EditApproximation.Refinement.ComputedQuerySetup
import OAI.Combinatorics.EditApproximation.Queries.QueryGroupSetupSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryOptimizerSpace
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
open BinaryFraction

namespace BinaryFraction



theorem onlineParametersAllocation_le_work (word : List Bool) (hpos : 0 < bitWordValue word) :
    onlineParametersAllocation word ≤ (onlineParametersWithWork word hpos).2 := by
  have h5 := bitPowerAllocation_le_work word 5
  have h4 := bitPowerAllocation_le_work word 4
  unfold onlineParametersAllocation onlineParametersWithWork
  dsimp only
  omega



theorem refinementDecrementAllocation_le_work (word : List Bool) (hpos : 0 < bitWordValue word) :
    refinementDecrementAllocation word ≤ (refinementDecrementWithWork word hpos).2 :=
  Nat.add_le_add_right (bitPowerAllocation_le_work word 10) 1

end BinaryFraction



theorem scheduledRefinementAllocation_le_work (N pass : ℕ) :
    scheduledRefinementAllocation N pass ≤ (scheduledRefinementWordWithWork N pass).2 := by
  unfold scheduledRefinementAllocation scheduledRefinementWordWithWork
  split_ifs
  · have h := signedPowerTwoAllocation_le_work
      ((dyadicSeedExponent (smallLogExponent N) (computedSeedInitialExponent N) pass - smallLogExponent N : ℕ) : ℤ)
    dsimp only
    omega
  · decide



theorem refinementParameterAllocation_le_work (N pass : ℕ) (word : List Bool)
    (hpos : 0 < bitWordValue word) :
    refinementParameterAllocation N pass word ≤ (refinementParameterWordsWithWork N pass word hpos).2 := by
  have ho := onlineParametersAllocation_le_work word hpos
  have hf := scheduledRefinementAllocation_le_work N pass
  have hd := refinementDecrementAllocation_le_work word hpos
  unfold refinementParameterAllocation refinementParameterWordsWithWork
  dsimp only
  omega



theorem refinementBaseAllocation_le_work (word : List Bool) :
    refinementBaseAllocation word ≤ (refinementBaseWithWork word).2 := by
  have hp := bitPowerAllocation_le_work word 10
  have hi := bitAddAllocation_le_work (bitPowerWithWork word 10).1 [true] false
  have ht := trimBitWordAllocation_le_work (bitAddWithWork (bitPowerWithWork word 10).1 [true] false).1
  unfold refinementBaseAllocation refinementBaseWithWork
  dsimp only
  omega



theorem computedQueryPassAllocation_le_work (N pass : ℕ) :
    computedQueryPassAllocation N pass ≤ (computedQueryPassWithWork N pass).2 := by
  have hs := signedPowerTwoAllocation_le_work
    ((dyadicSeedExponent (smallLogExponent N) (computedSeedInitialExponent N) pass : ℕ) : ℤ)
  have hp := refinementParameterAllocation_le_work N pass (inputSmallLog N).bits
    (by rw [bitWordValue_bits]; exact Nat.two_pow_pos _)
  unfold computedQueryPassAllocation computedQueryPassWithWork scheduledSeedWordWithWork
  dsimp only
  omega



theorem computedQuerySetupAllocation_le_work (N : ℕ) :
    computedQuerySetupAllocation N ≤ (computedQuerySetupWithWork N).2 := by
  have hv := vectorMapAllocation_le_work (computedSeedPassCount N + 1)
    (fun i => computedQueryPassWithWork N i.val) (fun i => computedQueryPassAllocation N i.val)
    (fun i => computedQueryPassAllocation_le_work N i.val)
  have hb := refinementBaseAllocation_le_work (inputSmallLog N).bits
  unfold computedQuerySetupAllocation computedQuerySetupWithWork
  dsimp only
  omega

end EditApproximation

end OAI
