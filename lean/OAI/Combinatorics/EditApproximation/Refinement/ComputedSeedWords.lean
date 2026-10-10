import OAI.Combinatorics.EditApproximation.Refinement.ComputedRefinementWords
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

/-- The actual dyadic incoming approximation factor used by a seed pass. -/


theorem scheduledSeedWordWithWork_value (N pass : ℕ) :
    (scheduledSeedWordWithWork N pass).1.value = scheduledSeedFactor N pass := by
  simp only [scheduledSeedWordWithWork, BinaryFraction.signedPowerTwoWithWork_value,
    zpow_natCast, scheduledSeedFactor]

theorem scheduledSeedWordWithWork_bounds (N pass : ℕ) (hN : 0 < N)
    (hell : 8 ≤ inputSmallLog N) (hH : 64 ≤ inputHeight N) :
    (scheduledSeedWordWithWork N pass).1.width ≤ inputHeight N ^ 3 ∧
      (scheduledSeedWordWithWork N pass).2 ≤ inputHeight N ^ 3 := by
  have he : dyadicSeedExponent (smallLogExponent N) (computedSeedInitialExponent N) pass ≤
      computedSeedInitialExponent N := Nat.sub_le _ _
  have hi := computed_window_le_height_cube N hN hell (by omega)
  have hw := BinaryFraction.signedPowerTwoWithWork_width
    ((dyadicSeedExponent (smallLogExponent N) (computedSeedInitialExponent N) pass : ℕ) : ℤ)
  simp only [Int.natAbs_natCast] at hw
  constructor
  · exact hw.trans (by omega)
  · simp only [scheduledSeedWordWithWork, BinaryFraction.signedPowerTwoWithWork, Int.natCast_nonneg,
      ite_true, Int.toNat_natCast]
    omega

theorem scheduledSeedWordWithWork_range (N pass : ℕ) :
    1 ≤ (scheduledSeedWordWithWork N pass).1.value ∧
      (scheduledSeedWordWithWork N pass).1.value ≤ ((integerParameters N).initialFactor : ℚ) := by
  rw [scheduledSeedWordWithWork_value]
  constructor
  · exact one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 2)
  · rw [← computedSeed_initial_factor]
    exact pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (Nat.sub_le _ _)

end EditApproximation

end OAI
