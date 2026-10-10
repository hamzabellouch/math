import OAI.Combinatorics.EditApproximation.Coarse.CoarseGridArithmetic
import OAI.Combinatorics.EditApproximation.Binary.BinaryAffineGuard
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Boolean threshold arithmetic on the fixed denominator of one coarse
execution. Quotients use actual long division when compressed to that grid. -/

namespace EditApproximation
namespace BinaryFraction



 theorem coarseDivideWithWork_value (a divisor : BinaryFraction)
    (hden : (a.value / divisor.value).den ∣ bitWordValue a.denominator) :
    (coarseDivideWithWork a divisor).1.value = a.value / divisor.value := by
  unfold coarseDivideWithWork
  dsimp only
  rw [fixedDenominatorWithWork_value, divWithWork_value]
  simpa only [divWithWork_value] using hden

 theorem coarseDivideWithWork_den (a divisor : BinaryFraction) :
    (coarseDivideWithWork a divisor).1.representation.den = a.representation.den := by
  exact fixedDenominatorWithWork_den _ _ _

 theorem coarseDivideWithWork_cost (a divisor : BinaryFraction) (B : ℕ)
    (ha : a.width ≤ B) (hd : divisor.width ≤ B) :
    (coarseDivideWithWork a divisor).2 ≤ 1000000 * (B + 1) ^ 2 := by
  have hq := divWithWork_cost a divisor B ha hd
  have hqw := divWithWork_width_uniform a divisor B ha hd
  have had : a.denominator.length ≤ B := (le_max_right _ _).trans ha
  have hc := fixedDenominatorWithWork_cost (divWithWork a divisor).1 a.denominator
    a.denominator_pos (4 * B + 4) B hqw had
  change (divWithWork a divisor).2 + _ + 2 ≤ _
  nlinarith only [hq, hc, Nat.zero_le B]

 theorem coarseDivideWithWork_width (a divisor : BinaryFraction) (V B : ℕ)
    (hden : (a.value / divisor.value).den ∣ bitWordValue a.denominator)
    (hv : |a.value / divisor.value| ≤ V) (hb : a.denominator.length ≤ B) :
    (coarseDivideWithWork a divisor).1.width ≤ Nat.size V + 2 * B + 1 := by
  exact fixedDenominatorWithWork_width (divWithWork a divisor).1 a.denominator
    a.denominator_pos (by simpa only [divWithWork_value] using hden) V B
    (by simpa only [divWithWork_value] using hv) hb

/-- The exact branch and maximum used for each transformed child cell. -/


 theorem coarseContributionWithWork_value (threshold scale a : BinaryFraction) :
    (coarseContributionWithWork threshold scale a).1.value =
      coarseThresholdContribution threshold.value scale.value a.value := by
  by_cases h : threshold.value ≤ a.value
  · simp only [coarseContributionWithWork, (leWithWork_value _ _).mpr h, ite_true,
      maxWithWork_value, coarseThresholdContribution, h]
  · have ht : (leWithWork threshold a).1 = false :=
      Bool.eq_false_iff.mpr (fun hh => h ((leWithWork_value _ _).mp hh))
    simp only [coarseContributionWithWork, ht, Bool.false_eq_true, ite_false,
      coarseGridNatWithWork_value, Nat.cast_zero, coarseThresholdContribution, h]

 theorem coarseContributionWithWork_den (threshold scale a : BinaryFraction)
    (hden : scale.representation.den = a.representation.den) :
    (coarseContributionWithWork threshold scale a).1.representation.den = a.representation.den := by
  unfold coarseContributionWithWork
  dsimp only
  split_ifs
  · unfold maxWithWork
    dsimp only
    split_ifs
    · exact hden
    · rfl
  · exact coarseGridNatWithWork_den _ _ _

 theorem coarseContributionWithWork_cost (threshold scale a : BinaryFraction) (B : ℕ)
    (ht : threshold.width ≤ B) (hs : scale.width ≤ B) (ha : a.width ≤ B) :
    (coarseContributionWithWork threshold scale a).2 ≤ 2200 * (B + 1) ^ 2 := by
  have htest := leWithWork_cost threshold a B ht ha
  have hmax := maxWithWork_cost a scale B ha hs
  have hzero := coarseGridNatWithWork_cost a.denominator a.denominator_pos 0 B
    (by simp) ((le_max_right _ _).trans ha)
  unfold coarseContributionWithWork
  dsimp only
  split_ifs <;> nlinarith only [htest, hmax, hzero, Nat.zero_le B]

end BinaryFraction
end EditApproximation

end OAI
