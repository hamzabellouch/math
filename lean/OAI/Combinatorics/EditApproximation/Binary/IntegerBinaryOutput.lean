import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryOutput
import OAI.Combinatorics.EditApproximation.Binary.IntegerAlgorithm

namespace OAI

namespace EditApproximation

/-- Actual binary output on a fixed accepted finite draw. -/
def integerBinaryOutput (source target : List ℤ) (N : ℕ)
    (input : ComputedFamilyInput (source.map integerSymbolCode) (target.map integerSymbolCode) N) :=
  computedQueryAnswerWithWork (source.map integerSymbolCode) (target.map integerSymbolCode) N
    (integerOccurrenceIndex source target) (integerInputSymbolBits source target) (integerInputPositionBits target) input

theorem integerBinaryOutput_cost (source target : List ℤ) (N : ℕ)
    (epsilon : BinaryFraction) (hlarge : physicalLargeInput N epsilon)
    (hsize : source.length + target.length ≤ N)
    (input : ComputedFamilyInput (source.map integerSymbolCode) (target.map integerSymbolCode) N) :
    (integerBinaryOutput source target N input).2 ≤ N + inputHeight N ^ 10 := by
  have hf : 3 ≤ smallLogExponent N := by
    have h := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hlarge.2.1.1
    omega
  apply computedQueryAnswerWithWork_cost _ _ _ _ _ _ _
    (largeAccuracyInput_pos N epsilon.value hlarge.2.1) hlarge.2.1.1 hf
    (by simpa only [List.length_map] using hsize) hlarge.2.2
  · intro a ha
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    exact integerInputSymbolBits_fits source target z (List.mem_append_left _ hz)
  · intro a ha
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    exact integerInputSymbolBits_fits source target z (List.mem_append_right _ hz)
  · simpa only [List.length_map, integerInputPositionBits] using (Nat.lt_size_self target.length).le
  · rfl

theorem integerBinaryOutput_execution (source target : List ℤ) (N : ℕ)
    (epsilon : BinaryFraction) (hlarge : physicalLargeInput N epsilon)
    (hsize : source.length + target.length ≤ N)
    (execution : ComputedExecutionOutcome (source.map integerSymbolCode) (target.map integerSymbolCode) N) :
    bitWordValue (integerBinaryOutput source target N
      (computedExecutionAccepted _ _ N execution)).1 =
      computedFullAnswer (source.map integerSymbolCode) (target.map integerSymbolCode) N (.inr execution) := by
  apply computedQueryAnswerWithWork_execution _ _ _ epsilon hlarge
    (by simpa only [List.length_map] using hsize)
  · intro a ha
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    exact integerInputSymbolBits_fits source target z (List.mem_append_left _ hz)
  · intro a ha
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    exact integerInputSymbolBits_fits source target z (List.mem_append_right _ hz)
  · simpa only [List.length_map, integerInputPositionBits] using (Nat.lt_size_self target.length).le
  · rfl

end EditApproximation

end OAI
