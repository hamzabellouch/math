import OAI.Combinatorics.EditApproximation.Binary.BinaryMedianKernel
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The natural seed cache stores a trimmed result, so repeated median
passes do not accumulate leading zero words. The trimming scan is charged. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem seedMedianWithWork_value (N multiplier : ℕ) (values : List BinaryFraction) :
    bitWordValue (seedMedianWithWork N multiplier values).1 =
      min N (upperMedian (values.map fun a => ⌈(multiplier : ℚ) * a.value⌉₊)) := by
  simp only [seedMedianWithWork, trimBitWordWithWork_value, medianSeedWithWork_value]

theorem seedMedianWithWork_length (N multiplier : ℕ) (values : List BinaryFraction) :
    (seedMedianWithWork N multiplier values).1.length ≤ Nat.size N := by
  simp only [seedMedianWithWork, trimBitWordWithWork_length, medianSeedWithWork_value]
  exact Nat.size_le_size (Nat.min_le_left _ _)

def seedMedianBitBudget (n B : ℕ) : ℕ := medianSeedBitBudget n B + 12 * B + 14

theorem seedMedianWithWork_cost (N multiplier : ℕ) (values : List BinaryFraction) (B : ℕ)
    (hN : Nat.size N ≤ B) (hm : Nat.size multiplier + 2 ≤ B)
    (hv : ∀ a ∈ values, a.width ≤ B) :
    (seedMedianWithWork N multiplier values).2 ≤ seedMedianBitBudget values.length B := by
  have hmedian := medianSeedWithWork_bounds N multiplier values B hN hm hv
  have htrim := trimBitWordWithWork_cost (medianSeedWithWork N multiplier values).1
  change (medianSeedWithWork N multiplier values).2 +
    (trimBitWordWithWork (medianSeedWithWork N multiplier values).1).2 + 1 ≤ _
  unfold seedMedianBitBudget
  omega

end BinaryFraction
end EditApproximation

end OAI
