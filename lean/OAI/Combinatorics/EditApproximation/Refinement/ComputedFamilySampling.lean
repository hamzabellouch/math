import OAI.Combinatorics.EditApproximation.Refinement.ComputedFamilyMemoCode
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalFamilySampling

namespace OAI

namespace EditApproximation

 theorem computedFamilyRange_bits_le (source target : List ℕ) (N R : ℕ)
    (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (key : ComputedFamilyScalarKey source target N R) :
    rejectionBitCount (physicalFamilyRange target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
      (computedSeedPassCount N) (inputHeight N ^ 2) key) ≤ inputHeight N := by
  apply physicalFamilyRange_bits_le
  · change 2 ^ (heightExponent N / 20) ≤ 2 ^ inputHeight N
    apply Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
    exact (Nat.div_le_self _ _).trans (Nat.lt_two_pow_self.le)
  · exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hB)

end EditApproximation

end OAI
