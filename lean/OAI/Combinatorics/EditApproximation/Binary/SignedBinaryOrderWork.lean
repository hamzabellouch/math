import OAI.Combinatorics.EditApproximation.Binary.SignedBinaryWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Signed comparisons performed on Boolean magnitude words, including the
noncanonical negative-zero representation. -/

namespace EditApproximation
namespace SignedBinary



theorem nonzeroWithWork_value (bits : List Bool) :
    (nonzeroWithWork bits).1 = true ↔ bitWordValue bits ≠ 0 := by
  simp [nonzeroWithWork, bitCompareWithWork_eq, bitWordValue]



theorem ltWithWork_value (a b : SignedBinary) :
    (a.ltWithWork b).1 = true ↔ a.value < b.value := by
  cases ha : a.negative <;> cases hb : b.negative
  · simp [ltWithWork, ha, hb, value, signedMagnitude, bitCompareWithWork_lt]
  · simp [ltWithWork, ha, hb, value, signedMagnitude]
  · simp only [ltWithWork, ha, hb, ↓reduceIte, Bool.false_eq_true,
      Bool.or_eq_true, nonzeroWithWork_value, value, signedMagnitude]
    omega
  · simp [ltWithWork, ha, hb, value, signedMagnitude, bitCompareWithWork_lt]

theorem nonzeroWithWork_cost (bits : List Bool) :
    (nonzeroWithWork bits).2 ≤ 4 * bits.length + 2 := by
  have h := bitCompareWithWork_cost bits []
  simp only [List.length_nil, Nat.add_zero] at h
  change (bitCompareWithWork bits []).2 + 1 ≤ _
  omega

theorem ltWithWork_cost (a b : SignedBinary) :
    (a.ltWithWork b).2 ≤ 4 * (a.bits.length + b.bits.length) + 8 := by
  have hab := bitCompareWithWork_cost a.bits b.bits
  have hba := bitCompareWithWork_cost b.bits a.bits
  have ha := nonzeroWithWork_cost a.bits
  have hb := nonzeroWithWork_cost b.bits
  cases hna : a.negative <;> cases hnb : b.negative <;>
    simp only [ltWithWork, hna, hnb, Bool.false_eq_true, ↓reduceIte] <;> omega

end SignedBinary
end EditApproximation

end OAI
