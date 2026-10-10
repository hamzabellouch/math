import OAI.Combinatorics.EditApproximation.Geometry.IndexedTerminalWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryDistanceWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

/-- The indexed terminal result is written directly as a binary rational. -/


theorem indexedLeafWithWork_le (table : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (symbol : Option ℕ) (lo hi : ℕ) :
    (indexedLeafWithWork table symbolBits positionBits symbol lo hi).1 ≤ hi + 1 := by
  rw [indexedLeafWithWork_value]
  cases symbol with
  | none => change hi - lo ≤ hi + 1; omega
  | some a =>
    simp only [indexedLeafCost, indexedSingletonCost]
    split_ifs <;> omega

theorem binaryIndexedLeafWithWork_value (table : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (symbol : Option ℕ) (lo hi : ℕ) :
    (binaryIndexedLeafWithWork table symbolBits positionBits symbol lo hi).1.value =
      (indexedLeafCost table symbolBits positionBits symbol lo hi : ℚ) := by
  simp only [binaryIndexedLeafWithWork, BinaryFraction.nat_value, indexedLeafWithWork_value]

theorem binaryIndexedLeafWithWork_bounds (table : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (symbol : Option ℕ) (lo hi : ℕ) :
    (binaryIndexedLeafWithWork table symbolBits positionBits symbol lo hi).1.width ≤ Nat.size (hi + 1) + 2 ∧
    (binaryIndexedLeafWithWork table symbolBits positionBits symbol lo hi).2 ≤
      2 * symbolBits + 4 * positionBits + Nat.size (hi + 1) + 12 := by
  have hv := Nat.size_le_size (indexedLeafWithWork_le table symbolBits positionBits symbol lo hi)
  have hc := indexedLeafWithWork_cost table symbolBits positionBits symbol lo hi
  constructor
  · exact (BinaryFraction.nat_width_le _).trans (Nat.add_le_add_right hv 2)
  · change _ + _ + 2 ≤ _
    omega

theorem integerBinaryIndexedLeafWithWork_cost (C : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ source target : List ℤ, source.length + target.length ≤ N →
      (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) → ∀ symbol lo hi, hi ≤ N →
      (binaryIndexedLeafWithWork (integerOccurrenceIndex source target) (integerInputSymbolBits source target)
        (integerInputPositionBits target) symbol lo hi).2 ≤ inputHeight N ^ 4 := by
  filter_upwards [integerIndexedLeafWithWork_cost C,
    inputHeight_real_tendsto.eventually (Filter.eventually_ge_atTop (100 : ℝ))] with N hc hH
  have hH' : 100 ≤ inputHeight N := by exact_mod_cast hH
  intro source target hsize halphabet symbol lo hi hhi
  have hcost := hc source target hsize halphabet symbol lo hi
  have hval := indexedLeafWithWork_le (integerOccurrenceIndex source target)
    (integerInputSymbolBits source target) (integerInputPositionBits target) symbol lo hi
  have hbits : Nat.size (indexedLeafWithWork (integerOccurrenceIndex source target)
      (integerInputSymbolBits source target) (integerInputPositionBits target) symbol lo hi).1 ≤
      inputHeight N + 1 :=
    (Nat.size_le_size (hval.trans (by omega))).trans (input_length_bits_le N)
  have hp := Nat.mul_le_mul_right (inputHeight N ^ 3) hH'
  have hh : inputHeight N ≤ inputHeight N ^ 3 := Nat.le_pow (by decide)
  change _ + _ + 2 ≤ _
  nlinarith only [hcost, hbits, hp, hh, hH']

end EditApproximation

end OAI
