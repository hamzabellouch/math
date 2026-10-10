import OAI.Combinatorics.EditApproximation.Probability.FiniteBufferRanges
import OAI.Combinatorics.EditApproximation.Geometry.RefinementBandSupport

namespace OAI

/-! The actual earlier-history gather projects into the child-initial
gather.  Consequently its default-zero word table retains the required
history bounds, even at coordinates absent from both finite buffers. -/

namespace EditApproximation

theorem queryEarlierInputCover_initial {nx ny M : ℕ}
    (parent : TargetInterval nx) (N P F exponent history : ℕ) (a : ℚ)
    (initial : TargetInterval ny → ℚ) (q : TargetInterval ny)
    (input : Fin M × ℕ × TargetInterval ny)
    (hinput : input ∈ queryEarlierInputCover parent N P F exponent history a initial q) :
    (input.1, input.2.2) ∈ refinementBandInputList parent N P F exponent a initial q := by
  obtain ⟨br, hbr, hinput⟩ := Finset.mem_biUnion.mp hinput
  obtain ⟨i, _, hinput⟩ := Finset.mem_biUnion.mp hinput
  obtain ⟨s, _, hinput⟩ := Finset.mem_biUnion.mp hinput
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hinput
  apply List.mem_eraseDups.mpr
  apply List.mem_flatMap.mpr
  refine ⟨br, List.mem_toFinset.mp hbr, List.mem_flatMap.mpr ?_⟩
  exact ⟨i, List.mem_finRange i, List.mem_map.mpr ⟨r, List.mem_toFinset.mp hr, rfl⟩⟩

namespace BinaryFraction

theorem gatheredRefinementHistory_range {nx ny M : ℕ}
    (parent : TargetInterval nx) (N P F exponent history : ℕ) (a : ℚ)
    (parentInitial : TargetInterval ny → ℚ) (q : TargetInterval ny)
    (equalHistory : (Fin M × ℕ × TargetInterval ny) →
      (Fin M × ℕ × TargetInterval ny) → Bool × ℕ)
    (equalChild : (Fin M × TargetInterval ny) → (Fin M × TargetInterval ny) → Bool × ℕ)
    (heh : ∀ x y, (equalHistory x y).1 = true ↔ x = y)
    (hec : ∀ x y, (equalChild x y).1 = true ↔ x = y)
    (historical : Fin M × ℕ × TargetInterval ny → BinaryFraction)
    (initial : Fin M × TargetInterval ny → BinaryFraction)
    (hnonneg : ∀ input, 0 ≤ (historical input).value)
    (hinitial : ∀ input, 0 ≤ (initial input).value)
    (hbound : ∀ input, (historical input).value ≤ (initial (input.1, input.2.2)).value)
    (input : Fin M × ℕ × TargetInterval ny) :
    let earlierKeys := orderedInputs historyInputCode (historyInputCode_injective M ny)
      (queryEarlierInputCover parent N P F exponent history a parentInitial q)
    let initialKeys := refinementBandInputList (M := M) parent N P F exponent a parentInitial q
    0 ≤ (gatheredWordLookupWithWork equalHistory earlierKeys (earlierKeys.map historical) input).1.value ∧
      (gatheredWordLookupWithWork equalHistory earlierKeys (earlierKeys.map historical) input).1.value ≤
        (gatheredWordLookupWithWork equalChild initialKeys (initialKeys.map initial)
          (input.1, input.2.2)).1.value := by
  dsimp only
  rw [gatheredWordLookupWithWork_value equalHistory heh,
    gatheredWordLookupWithWork_value equalChild hec]
  simp only [List.map_map, Function.comp_def]
  let earlierKeys := orderedInputs historyInputCode (historyInputCode_injective M ny)
    (queryEarlierInputCover parent N P F exponent history a parentInitial q)
  let initialKeys := refinementBandInputList (M := M) parent N P F exponent a parentInitial q
  change 0 ≤ finiteAnswerTable earlierKeys (earlierKeys.map fun x => (historical x).value) input ∧
    finiteAnswerTable earlierKeys (earlierKeys.map fun x => (historical x).value) input ≤
      finiteAnswerTable initialKeys (initialKeys.map fun x => (initial x).value) (input.1, input.2.2)
  constructor
  · apply finiteAnswerTable_nonneg
    intro value hv
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp hv
    exact hnonneg key
  · by_cases hinput : input ∈ earlierKeys
    · have hp : (input.1, input.2.2) ∈ initialKeys :=
        queryEarlierInputCover_initial parent N P F exponent history a parentInitial q input
          ((mem_orderedInputs historyInputCode (historyInputCode_injective M ny) _ input).mp hinput)
      rw [finiteAnswerTable_map earlierKeys _ input hinput,
        finiteAnswerTable_map initialKeys _ _ hp]
      exact hbound input
    · rw [finiteAnswerTable_eq_zero_of_not_mem earlierKeys _ input hinput]
      apply finiteAnswerTable_nonneg
      intro value hv
      obtain ⟨key, _, rfl⟩ := List.mem_map.mp hv
      exact hinitial key

end BinaryFraction
end EditApproximation

end OAI
