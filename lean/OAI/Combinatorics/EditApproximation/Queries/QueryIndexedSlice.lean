import OAI.Combinatorics.EditApproximation.Binary.BinaryIndexedLeaf
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLeaves
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! A terminal source interval is accessed through its stored endpoint.
Its substring is used only in the specification, never materialized. -/

namespace EditApproximation



@[simp] theorem querySliceHeadWithWork_value {α : Type*} (source : List α)
    (interval : TargetInterval source.length) :
    (querySliceHeadWithWork source interval).1 = (substring source interval.lo interval.hi).head? := by
  unfold querySliceHeadWithWork substring
  dsimp only
  rw [List.head?_drop, List.getElem?_take]
  by_cases h : interval.lo < interval.hi
  · rw [ite_eq_left ((binaryNaturalCompareWithWork_lt _ _).mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hc => h ((binaryNaturalCompareWithWork_lt _ _).mp hc)), ite_eq_right h]

theorem querySliceHeadWithWork_cost {α : Type*} (source : List α)
    (interval : TargetInterval source.length) (B : ℕ) (hB : Nat.size source.length ≤ B) :
    (querySliceHeadWithWork source interval).2 ≤ 10 * B + 4 := by
  have hl := (Nat.size_le_size (interval.ordered.trans interval.valid)).trans hB
  have hh := (Nat.size_le_size interval.valid).trans hB
  have hc := binaryNaturalCompareWithWork_cost interval.lo interval.hi
  change _ + _ + _ + 3 ≤ _
  omega



theorem queryIndexedSliceWithWork_value (source target : List ℕ)
    (interval : TargetInterval source.length) (q : TargetInterval target.length)
    (symbolBits positionBits : ℕ)
    (hs : ∀ a ∈ source, a < 2 ^ symbolBits) (ht : ∀ a ∈ target, a < 2 ^ symbolBits)
    (hp : target.length ≤ 2 ^ positionBits) :
    (queryIndexedSliceWithWork source interval target.length q
      (occurrenceBuild symbolBits positionBits target.zipIdx) symbolBits positionBits).1.value =
      (shortSourceCost (substring source interval.lo interval.hi) (substring target q.lo q.hi) : ℚ) := by
  simp only [queryIndexedSliceWithWork, binaryIndexedLeafWithWork_value, querySliceHeadWithWork_value]
  congr 1
  apply indexedLeafCost_eq symbolBits positionBits _ target _ ht hp q.lo q.hi q.ordered q.valid
  intro a ha
  exact hs a (List.mem_of_mem_take (List.mem_of_mem_drop ha))

theorem queryIndexedSliceWithWork_cost (source : List ℕ)
    (interval : TargetInterval source.length) (targetLength : ℕ) (q : TargetInterval targetLength)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits B : ℕ)
    (hB : Nat.size source.length ≤ B) :
    (queryIndexedSliceWithWork source interval targetLength q occurrence symbolBits positionBits).2 ≤
      10 * B + 2 * symbolBits + 4 * positionBits + Nat.size (targetLength + 1) + 17 := by
  have hs := querySliceHeadWithWork_cost source interval B hB
  have hr := (binaryIndexedLeafWithWork_bounds occurrence symbolBits positionBits
    (querySliceHeadWithWork source interval).1 q.lo q.hi).2
  have hh := Nat.size_le_size (Nat.add_le_add_right q.valid 1)
  change (querySliceHeadWithWork source interval).2 + _ + 1 ≤ _
  omega

end EditApproximation

end OAI
