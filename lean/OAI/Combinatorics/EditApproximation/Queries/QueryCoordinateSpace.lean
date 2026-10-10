import OAI.Combinatorics.EditApproximation.Queries.QueryBufferSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryCoordinateAction
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

/-- The spare loop charge also covers the input index-list spine. -/
theorem arithmeticMapAllocation_with_spine {α β : Type*} (f : α → β × ℕ)
    (allocation : α → ℕ) (values : List α) (h : ∀ a ∈ values, allocation a ≤ (f a).2) :
    arithmeticMapAllocation allocation values + values.length ≤ (arithmeticMapWithWork f values).2 := by
  induction values with
  | nil => exact Nat.zero_le _
  | cons a rest ih =>
    have ha := h a List.mem_cons_self
    have ht := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [arithmeticMapAllocation, arithmeticMapWithWork, List.length_cons]
    omega



theorem memberByAllocation_le_work {α : Type*} (equal : α → α → Bool × ℕ)
    (allocation : α → α → ℕ) (a : α) (values : List α)
    (h : ∀ b ∈ values, allocation a b ≤ (equal a b).2) :
    memberByAllocation allocation a values ≤ (memberByWithWork equal a values).2 := by
  induction values with
  | nil => exact Nat.zero_le _
  | cons b rest ih =>
    have hb := h b List.mem_cons_self
    have ht := ih (fun c hc => h c (List.mem_cons_of_mem _ hc))
    simp only [memberByAllocation, memberByWithWork]
    omega



theorem dedupByAllocation_le_work {α : Type*} (equal : α → α → Bool × ℕ)
    (allocation : α → α → ℕ) (values : List α) (h : ∀ a b, allocation a b ≤ (equal a b).2) :
    dedupByAllocation equal allocation values ≤ (dedupByWithWork equal values).2 := by
  induction values with
  | nil => exact Nat.zero_le _
  | cons a rest ih =>
    have hm := memberByAllocation_le_work equal allocation a rest (fun b _ => h a b)
    simp only [dedupByAllocation, dedupByWithWork]
    split_ifs <;> omega

namespace BinaryFraction



theorem bandCoordinatesAllocation_le_work {M n : ℕ} (band : List (Fin M → TargetInterval n)) :
    bandCoordinatesAllocation band ≤ (bandCoordinatesWithWork band).2 := by
  let build := fun action : Fin M → TargetInterval n =>
    arithmeticMapWithWork (fun i : Fin M => ((i, action i), 1)) (List.finRange M)
  have hr := arithmeticFlatMapAllocation_le_work build
    (fun _ => arithmeticMapAllocation (fun _ : Fin M => 1) (List.finRange M) + M) band (by
      intro action _
      simpa only [List.length_finRange] using arithmeticMapAllocation_with_spine
        (fun i : Fin M => ((i, action i), 1)) (fun _ => 1) (List.finRange M) (fun _ _ => le_rfl))
  have hd := dedupByAllocation_le_work coordinateEqualWithWork coordinateEqualAllocation
    (arithmeticFlatMapWithWork build band).1 coordinateEqualAllocation_le_work
  unfold bandCoordinatesAllocation bandCoordinatesWithWork
  dsimp only [build] at hr hd ⊢
  omega



theorem coordinateVectorAllocation_le_work {M n : ℕ} (band : List (Fin M → TargetInterval n)) :
    coordinateVectorAllocation band ≤ (coordinateVectorWithWork band).2 := by
  have h := bandCoordinatesAllocation_le_work band
  unfold coordinateVectorAllocation coordinateVectorWithWork
  dsimp only
  omega

end BinaryFraction
end EditApproximation

end OAI
