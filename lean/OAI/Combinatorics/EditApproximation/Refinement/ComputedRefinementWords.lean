import OAI.Combinatorics.EditApproximation.Refinement.ComputedBinaryOnlineParameters
import OAI.Combinatorics.EditApproximation.Binary.BinaryRefinementParameters
import OAI.Combinatorics.EditApproximation.Binary.BinaryGroupSetup
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalSeedSchedule
import OAI.Combinatorics.EditApproximation.Geometry.ParameterLocalAsymptotics
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

/-- The scheduled integer refinement factor is materialized by its dyadic
exponent; the terminal pass materializes one. -/


theorem scheduledRefinementWordWithWork_value (N pass : ℕ)
    (hf : 3 ≤ smallLogExponent N) (hpass : pass ≤ computedSeedPassCount N) :
    (scheduledRefinementWordWithWork N pass).1.value =
      refinementFactor (scheduledSeedFactor N pass) (inputSmallLog N) := by
  unfold scheduledRefinementWordWithWork
  split_ifs with h
  · simp only [BinaryFraction.signedPowerTwoWithWork_value, zpow_natCast]
    rw [← scheduledSeedMultiplier_spec N pass hf h]
    simp only [scheduledSeedMultiplier, Nat.cast_pow, Nat.cast_ofNat]
  · have heq : pass = computedSeedPassCount N := by omega
    rw [heq, scheduledSeedFactor_terminal_refinement N hf]
    exact BinaryFraction.nat_value 1

theorem scheduledRefinementWordWithWork_bounds (N pass : ℕ) (hH : 64 ≤ inputHeight N) :
    (scheduledRefinementWordWithWork N pass).1.width ≤ inputHeight N ^ 3 ∧
      (scheduledRefinementWordWithWork N pass).2 ≤ inputHeight N ^ 3 := by
  let H := inputHeight N
  change (scheduledRefinementWordWithWork N pass).1.width ≤ H ^ 3 ∧
    (scheduledRefinementWordWithWork N pass).2 ≤ H ^ 3
  have hp : coarseExponent (inputSmallLog N) ≤ H :=
    (coarseExponent_le_smallLog N).trans (computed_smallLog_le_height N)
  have he : heightExponent N ≤ H := Nat.lt_two_pow_self.le
  have hinitial : computedSeedInitialExponent N + 8 ≤ H ^ 3 := by
    unfold computedSeedInitialExponent
    have hm := Nat.mul_le_mul (Nat.add_le_add_right hp 4) he
    change 64 ≤ H at hH
    have hc : 3 * H ^ 2 ≤ H ^ 3 := by
      calc
        _ ≤ H * H ^ 2 := Nat.mul_le_mul_right (H ^ 2) (show 3 ≤ H by omega)
        _ = _ := by ring
    nlinarith only [hm, hH, hc]
  unfold scheduledRefinementWordWithWork
  split_ifs
  · have he' : dyadicSeedExponent (smallLogExponent N) (computedSeedInitialExponent N) pass -
        smallLogExponent N ≤ computedSeedInitialExponent N :=
      (Nat.sub_le _ _).trans (Nat.sub_le _ _)
    have hw := BinaryFraction.signedPowerTwoWithWork_width
      ((dyadicSeedExponent (smallLogExponent N) (computedSeedInitialExponent N) pass - smallLogExponent N : ℕ) : ℤ)
    simp only [Int.natAbs_natCast] at hw
    constructor
    · exact hw.trans (by omega)
    · simp only [BinaryFraction.signedPowerTwoWithWork, Int.natCast_nonneg, ite_true, Int.toNat_natCast]
      omega
  · have hw := BinaryFraction.nat_width_le 1
    have h3 : 3 ≤ H ^ 3 := (by omega : 3 ≤ H).trans (Nat.le_pow (by decide))
    exact ⟨hw.trans (by simpa only [Nat.size_one] using h3), h3⟩

/-- Width and range bounds for all five constructed scalar words. Tau and
kappa share the same reciprocal fourth-power word. -/
theorem computedRefinementWords_bounds (N pass : ℕ) (word : List Bool)
    (hvalue : bitWordValue word = inputSmallLog N)
    (hwidth : word.length ≤ Nat.size (inputSmallLog N))
    (hH : 64 ≤ inputHeight N) (hpositive : 0 < bitWordValue word) :
    let parameters := BinaryFraction.onlineParametersWithWork word hpositive
    parameters.1.2.width ≤ inputHeight N ^ 8 ∧
    (scheduledRefinementWordWithWork N pass).1.width ≤ inputHeight N ^ 8 ∧
    parameters.1.1.width ≤ inputHeight N ^ 8 ∧
    (BinaryFraction.refinementDecrementWithWork word hpositive).1.width ≤ inputHeight N ^ 8 ∧
    |parameters.1.1.value| ≤ ((inputHeight N ^ 5 : ℕ) : ℚ) ∧
    0 ≤ parameters.1.2.value ∧ parameters.1.2.value ≤ 1 := by
  have hc := computedBinaryOnlineParameters_caps N word hvalue hwidth hH hpositive
  have hword : word.length ≤ inputHeight N := hwidth.trans
    ((Nat.size_le.mpr Nat.lt_two_pow_self).trans (computed_smallLog_le_height N))
  have hd := (BinaryFraction.refinementDecrementWithWork_cap word hpositive (inputHeight N) hH hword).1
  have ha := (scheduledRefinementWordWithWork_bounds N pass hH).1
  have h2 : inputHeight N ^ 2 ≤ inputHeight N ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  have h3 : inputHeight N ^ 3 ≤ inputHeight N ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  exact ⟨hc.2.1.trans h2, ha.trans h3, hc.1.trans h2, hd.trans h2, hc.2.2⟩



/-- Concrete construction of the scalar words consumed by the local kernel. -/


theorem refinementParameterWordsWithWork_values (N pass : ℕ) (word : List Bool)
    (hpositive : 0 < bitWordValue word) (hvalue : bitWordValue word = inputSmallLog N)
    (hf : 3 ≤ smallLogExponent N) (hpass : pass ≤ computedSeedPassCount N) :
    let values := (refinementParameterWordsWithWork N pass word hpositive).1
    values.tau.value = (rationalParameters (inputSmallLog N)).tau ∧
      values.factor.value = refinementFactor (scheduledSeedFactor N pass) (inputSmallLog N) ∧
      values.eta.value = (rationalParameters (inputSmallLog N)).eta ∧
      values.kappa.value = (rationalParameters (inputSmallLog N)).kappa ∧
      values.delta.value = (rationalParameters (inputSmallLog N)).delta := by
  simp only [refinementParameterWordsWithWork, BinaryFraction.onlineParametersWithWork_kappa,
    BinaryFraction.onlineParametersWithWork_eta, BinaryFraction.refinementDecrementWithWork_value,
    scheduledRefinementWordWithWork_value N pass hf hpass, hvalue]
  simp [rationalParameters]

theorem refinementParameterWordsWithWork_cost (N pass : ℕ) (word : List Bool)
    (hpositive : 0 < bitWordValue word)
    (hwidth : word.length ≤ Nat.size (inputSmallLog N)) (hH : 64 ≤ inputHeight N) :
    (refinementParameterWordsWithWork N pass word hpositive).2 ≤ inputHeight N ^ 9 := by
  have ho := computedBinaryOnlineParameters_cost N word hwidth hH hpositive
  have hf := (scheduledRefinementWordWithWork_bounds N pass hH).2
  have hw : word.length ≤ inputHeight N := hwidth.trans
    ((Nat.size_le.mpr Nat.lt_two_pow_self).trans (computed_smallLog_le_height N))
  have hd := (BinaryFraction.refinementDecrementWithWork_cap word hpositive (inputHeight N) hH hw).2
  have hp : inputHeight N ^ 3 ≤ inputHeight N ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  have hunit : 1 ≤ inputHeight N ^ 8 := one_le_pow₀ (by omega)
  have hmul := Nat.mul_le_mul_right (inputHeight N ^ 8) (show 8 ≤ inputHeight N by omega)
  simp only [refinementParameterWordsWithWork]
  rw [pow_succ]
  nlinarith only [ho, hf, hd, hp, hunit, hmul]

end EditApproximation

end OAI
