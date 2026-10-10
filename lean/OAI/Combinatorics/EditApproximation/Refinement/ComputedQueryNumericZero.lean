import OAI.Combinatorics.EditApproximation.Refinement.ComputedPreparedInputBounds

namespace OAI

namespace EditApproximation
open Filter

theorem computedQueryNumeric_zero :
    ∀ᶠ N : ℕ in atTop, BinaryFraction.PreparedKernelNumericBounds (nx := 0) (ny := 0)
      (M := (integerParameters N).M) N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
      (heightExponent N / 20) (smallLogExponent N) (inputHeight N ^ 8) (inputHeight N ^ 5)
      (inputHeight N ^ ((100 * (integerParameters N).M + 100000) * (coarseExponent (inputSmallLog N) + 1)))
      0 BinaryFraction.zero BinaryFraction.zero BinaryFraction.zero BinaryFraction.zero BinaryFraction.zero
      (fun _ _ => 0) := by
  filter_upwards [computedPreparedNumericBounds,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 64)] with N hn hell
  have hH : 64 ≤ inputHeight N := hell.trans (computed_smallLog_le_height N)
  have hz : BinaryFraction.zero.width ≤ inputHeight N ^ 8 := by
    change 1 ≤ inputHeight N ^ 8
    exact one_le_pow₀ (by omega)
  have hzv : BinaryFraction.zero.value = 0 := by
    norm_num [BinaryFraction.value, BinaryFraction.zero, SignedBinary.value, signedMagnitude, bitWordValue]
  exact hn 0 0 (by omega) 0 (by omega) _ _ _ _ _ hz hz hz hz hz
    (by rw [hzv]; simp) (by rw [hzv]; norm_num) (fun _ _ => 0) (by intro b r; simp)

end EditApproximation

end OAI
