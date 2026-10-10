import OAI.Combinatorics.EditApproximation.Geometry.ParameterNumericalConstruction
import OAI.Combinatorics.EditApproximation.Binary.BinaryAffineGuard
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalUniformAccuracy
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

/-- Prefix rejection precedes arithmetic involving the accuracy word. -/


 theorem physicalLargeInputWithWork_value (N : ℕ) (epsilon : BinaryFraction) :
    (physicalLargeInputWithWork N epsilon).1 = decide (physicalLargeInput N epsilon) := by
  apply Bool.eq_iff_iff.mpr
  by_cases hi : (inspectAccuracyWithWork (inputHeight N) epsilon).1.isSome = true
  · have hc : (binaryNaturalCompareWithWork (inputSmallLog N) (2 ^ 1000)).1 ≠ .lt ↔
        2 ^ 1000 ≤ inputSmallLog N := by
      rw [ne_eq, binaryNaturalCompareWithWork_lt, not_lt]
    have ha : (BinaryFraction.ltWithWork
        (BinaryFraction.canonicalMulWithWork (BinaryFraction.nat (inputSmallLog N)) epsilon).1
        (BinaryFraction.nat 10)).1 ≠ true ↔ 10 ≤ (inputSmallLog N : ℚ) * epsilon.value := by
      rw [ne_eq, BinaryFraction.ltWithWork_value, BinaryFraction.canonicalMulWithWork_value,
        BinaryFraction.nat_value, BinaryFraction.nat_value, not_lt]
      norm_num
    have hm : (binaryNaturalCompareWithWork (inputHeight N)
        (inputBitLengthWithWork
          (onlineMassWithWork (integerParameters N).M (integerParameters N).P (inputHeight N)).1).1).1 ≠ .lt ↔
        Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
          (inputHeight N)) ≤ inputHeight N := by
      rw [ne_eq, binaryNaturalCompareWithWork_lt, inputBitLengthWithWork_spec,
        onlineMassWithWork_value, not_lt]
    simp only [physicalLargeInputWithWork, hi, ite_true, decide_eq_true_eq,
      physicalLargeInput, largeAccuracyInput, hc, ha, hm, true_and, and_assoc]
  · simp only [physicalLargeInputWithWork, hi, ite_false, Bool.false_eq_true, decide_eq_true_eq,
      physicalLargeInput, false_and]

 theorem physicalLargeInputWithWork_cost (N : ℕ) (epsilon : BinaryFraction)
    (hmass : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N) :
    (physicalLargeInputWithWork N epsilon).2 ≤ 100000 * (inputHeight N + 1005) ^ 2 := by
  let B := (inputHeight N) + 1005
  have hi := inspectAccuracyWithWork_cost (inputHeight N) epsilon
  by_cases haccepted : (inspectAccuracyWithWork (inputHeight N) epsilon).1.isSome = true
  · have hepsilon : epsilon.width ≤ (inputHeight N) := by
      rw [inspectAccuracyWithWork_spec] at haccepted
      split_ifs at haccepted with he
      · exact he
      · cases haccepted
    have hell : Nat.size (inputSmallLog N) + 2 ≤ B := by
      have hs := Nat.size_le_size (computed_smallLog_le_height N)
      have hh : Nat.size (inputHeight N) ≤ (inputHeight N) + 1 := by
        apply Nat.size_le.mpr
        exact Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ (inputHeight N)))
      dsimp only [B]
      omega
    have hleft : (BinaryFraction.nat (inputSmallLog N)).width ≤ B :=
      (BinaryFraction.nat_width_le _).trans hell
    have hright : epsilon.width ≤ B := hepsilon.trans (by dsimp [B]; omega)
    have hten : (BinaryFraction.nat 10).width ≤ 4 * B + 2 := by
      have ht := BinaryFraction.nat_width_le 10
      rw [show Nat.size 10 = 4 from by decide] at ht
      dsimp only [B]
      omega
    have hp := BinaryFraction.canonicalMulWithWork_cost
      (BinaryFraction.nat (inputSmallLog N)) epsilon B hleft hright
    have hpw := BinaryFraction.canonicalMulWithWork_width
      (BinaryFraction.nat (inputSmallLog N)) epsilon B hleft hright
    have ha := BinaryFraction.ltWithWork_cost
      (BinaryFraction.canonicalMulWithWork (BinaryFraction.nat (inputSmallLog N)) epsilon).1
      (BinaryFraction.nat 10) (4 * B + 2) hpw hten
    have ht := binaryNaturalCompareWithWork_cost (inputSmallLog N) (2 ^ 1000)
    have hc := binaryNaturalCompareWithWork_cost (inputHeight N)
      (Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P (inputHeight N)))
    have hHsize : Nat.size (inputHeight N) ≤ (inputHeight N) + 1 := by
      apply Nat.size_le.mpr
      exact Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ (inputHeight N)))
    have hmsize : Nat.size (Nat.size (localOnlineMassBound (integerParameters N).M
        (integerParameters N).P (inputHeight N))) ≤ (inputHeight N) + 1 := (Nat.size_le_size hmass).trans hHsize
    simp only [Nat.size_pow] at ht
    simp only [physicalLargeInputWithWork, haccepted, ite_true, inputBitLengthWithWork_spec,
      onlineMassWithWork_value, onlineMassWithWork_cost]
    change _ ≤ 100000 * B ^ 2
    dsimp only [B] at hp ha hell ⊢
    nlinarith only [hp, ha, ht, hi, hc, hHsize, hmsize, hmass, hell]
  · simp only [physicalLargeInputWithWork, haccepted, Bool.false_eq_true, ite_false]
    nlinarith only [hi, Nat.zero_le (inputHeight N)]

end EditApproximation

end OAI
