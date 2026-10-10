import OAI.Combinatorics.EditApproximation.Coarse.CoarseCellBounds

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- A zero marker or one full shift array on the execution's common grid. -/
def CoarseBinaryBox (two : BinaryFraction) (n V D A : ℕ) (array : CoarseBinaryArray) : Prop :=
  ∀ cells, array = some cells → cells.length = n ∧ ∀ a ∈ cells, CoarseGridCell two a V D A

 theorem coarseBinaryBox_none (two : BinaryFraction) (n V D A : ℕ) :
    CoarseBinaryBox two n V D A none := by
  intro cells h; cases h

 theorem coarseBinaryBox_mono (two : BinaryFraction) (n V W D A : ℕ)
    (array : CoarseBinaryArray) (h : CoarseBinaryBox two n V D A array) (hle : V ≤ W) :
    CoarseBinaryBox two n W D A array := by
  intro cells hc
  exact ⟨(h cells hc).1, fun a ha => coarseGridCell_mono two a V W D A ((h cells hc).2 a ha) hle⟩

 theorem coarseGridZipAddWithWork_bounds (two : BinaryFraction) (left right : List BinaryFraction)
    (V W D A : ℕ) (hl : ∀ a ∈ left, CoarseGridCell two a V D A)
    (hr : ∀ a ∈ right, CoarseGridCell two a W D A)
    (hbound : Nat.size (V + W) + 2 * D + 1 ≤ A) :
    ∀ a ∈ (coarseGridZipAddWithWork left right).1, CoarseGridCell two a (V + W) D A := by
  induction left generalizing right with
  | nil => simp only [coarseGridZipAddWithWork, List.not_mem_nil, false_implies, implies_true]
  | cons a left ih =>
    cases right with
    | nil => simp only [coarseGridZipAddWithWork, List.not_mem_nil, false_implies, implies_true]
    | cons b right =>
      intro z hz
      change z ∈ (coarseGridAddWithWork a b).1 :: _ at hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact coarseGridAddWithWork_bounds two a b V W D A (hl a List.mem_cons_self)
          (hr b List.mem_cons_self) hbound
      · exact ih right (fun a ha => hl a (List.mem_cons_of_mem _ ha))
          (fun b hb => hr b (List.mem_cons_of_mem _ hb)) z hz

 theorem coarseGridZipAddWithWork_length (left right : List BinaryFraction) :
    (coarseGridZipAddWithWork left right).1.length = min left.length right.length := by
  induction left generalizing right with
  | nil => simp only [coarseGridZipAddWithWork, List.length_nil, Nat.zero_min]
  | cons a left ih =>
    cases right with
    | nil => simp only [coarseGridZipAddWithWork, List.length_nil, Nat.min_zero]
    | cons b right =>
      change _ + 1 = min _ _
      rw [ih]
      simp only [List.length_cons]
      omega

 theorem coarseBinaryAddWithWork_box (two : BinaryFraction) (n V W D A : ℕ)
    (left right : CoarseBinaryArray) (hl : CoarseBinaryBox two n V D A left)
    (hr : CoarseBinaryBox two n W D A right)
    (hbound : Nat.size (V + W) + 2 * D + 1 ≤ A) :
    CoarseBinaryBox two n (V + W) D A (coarseBinaryAddWithWork left right).1 := by
  cases left with
  | none => exact coarseBinaryBox_mono two n W (V + W) D A right hr (by omega)
  | some left =>
    cases right with
    | none => exact coarseBinaryBox_mono two n V (V + W) D A (some left) hl (by omega)
    | some right =>
      intro cells hc
      have heq : (coarseGridZipAddWithWork left right).1 = cells := Option.some.inj hc
      rw [← heq]
      refine ⟨?_, coarseGridZipAddWithWork_bounds two left right V W D A
        (hl left rfl).2 (hr right rfl).2 hbound⟩
      rw [coarseGridZipAddWithWork_length, (hl left rfl).1, (hr right rfl).1, min_self]

 theorem coarseBinaryAddWithWork_cost (two : BinaryFraction) (n V W D A : ℕ)
    (left right : CoarseBinaryArray) (hl : CoarseBinaryBox two n V D A left)
    (hr : CoarseBinaryBox two n W D A right) :
    (coarseBinaryAddWithWork left right).2 ≤ n * (100 * (A + 1) + 3) := by
  cases left with
  | none => change 0 ≤ _; omega
  | some left =>
    cases right with
    | none => change 0 ≤ _; omega
    | some right =>
      have h := coarseGridZipAddWithWork_cost left right A
        (fun a ha => ((hl left rfl).2 a ha).2.2.2.2)
        (fun b hb => ((hr right rfl).2 b hb).2.2.2.2)
      simpa only [coarseBinaryAddWithWork, (hl left rfl).1, (hr right rfl).1, min_self] using h

 theorem coarseBinaryPenaltyWithWork_box (two : BinaryFraction) (n V D A : ℕ)
    (array : CoarseBinaryArray) (h : CoarseBinaryBox two n V D A array)
    (htwo : two.value = 2) (htw : two.width ≤ A)
    (hbound : Nat.size (V + 2) + 2 * D + 1 ≤ A) :
    CoarseBinaryBox two n V D A (coarseBinaryPenaltyWithWork two array).1 := by
  cases array with
  | none => exact coarseBinaryBox_none two n V D A
  | some source =>
    intro cells hc
    have heq : (coarseGridPenaltyWithWork two source).1 = cells := Option.some.inj hc
    rw [← heq]
    refine ⟨?_, coarseGridPenaltyWithWork_bounds two source V D A htwo htw hbound (h source rfl).2⟩
    have hv := congrArg List.length (coarseGridPenaltyWithWork_value two source htwo
      (fun a ha => ((h source rfl).2 a ha).1))
    simpa only [List.length_map, coarsePenaltyTransform_length, (h source rfl).1] using hv

 theorem coarseBinaryPenaltyWithWork_cost (two : BinaryFraction) (n V D A : ℕ)
    (array : CoarseBinaryArray) (h : CoarseBinaryBox two n V D A array)
    (htwo : two.value = 2) (htw : two.width ≤ A)
    (hbound : Nat.size (V + 2) + 2 * D + 1 ≤ A) :
    (coarseBinaryPenaltyWithWork two array).2 ≤ n * (3500 * (A + 1) ^ 2 + 20) := by
  cases array with
  | none => change 0 ≤ _; omega
  | some source =>
    have hc := coarseGridPenaltyWithWork_cost two source V D A htwo htw hbound (h source rfl).2
    simpa only [coarseBinaryPenaltyWithWork, (h source rfl).1] using hc

 theorem coarseBinaryMapWithWork_box (two : BinaryFraction) (n V W D A : ℕ)
    (f : BinaryFraction → BinaryFraction × ℕ) (array : CoarseBinaryArray)
    (h : CoarseBinaryBox two n V D A array)
    (hf : ∀ a, CoarseGridCell two a V D A → CoarseGridCell two (f a).1 W D A) :
    CoarseBinaryBox two n W D A (coarseBinaryMapWithWork f array).1 := by
  cases array with
  | none => exact coarseBinaryBox_none two n W D A
  | some source =>
    intro cells hc
    have heq : (arithmeticMapWithWork f source).1 = cells := Option.some.inj hc
    rw [← heq, arithmeticMapWithWork_value]
    refine ⟨?_, ?_⟩
    · simpa only [List.length_map] using (h source rfl).1
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact hf b ((h source rfl).2 b hb)

 theorem coarseBinaryMapWithWork_cost (two : BinaryFraction) (n V D A C : ℕ)
    (f : BinaryFraction → BinaryFraction × ℕ) (array : CoarseBinaryArray)
    (h : CoarseBinaryBox two n V D A array)
    (hf : ∀ a, CoarseGridCell two a V D A → (f a).2 ≤ C) :
    (coarseBinaryMapWithWork f array).2 ≤ n * (C + 3) := by
  cases array with
  | none => change 0 ≤ _; omega
  | some source =>
    have hc := arithmeticMapWithWork_cost f source C (fun a ha => hf a ((h source rfl).2 a ha))
    simpa only [coarseBinaryMapWithWork, (h source rfl).1] using hc

end BinaryFraction
end EditApproximation

end OAI
