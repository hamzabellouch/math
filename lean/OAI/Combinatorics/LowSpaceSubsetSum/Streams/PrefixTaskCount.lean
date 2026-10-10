import OAI.Combinatorics.LowSpaceSubsetSum.Counting.ParentRestrictionUniverse
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.PrefixCheckList

namespace OAI

/-! # Task-start bounds for the executable prefix recursion -/

noncomputable section

namespace LowSpaceSubsetSum.RepresentationParentData

variable {n : ℕ} (D : RepresentationParentData n)

def overflowCount (B : ℕ) : List (Fin n) → MaskRestriction n → ℕ
  | order, P =>
    if ({ D with maskRestriction := P }.collect B).state.user.keys.overflow then
      match order with
      | [] => 1
      | i :: rest => 1 + overflowCount B rest (P.force i false) + overflowCount B rest (P.force i true)
    else 0

def taskStarts (B : ℕ) : List (Fin n) → MaskRestriction n → ℕ
  | [], _ => 1
  | i :: rest, P =>
    if ({ D with maskRestriction := P }.collect B).state.user.keys.overflow then
      1 + taskStarts B rest (P.force i false) + taskStarts B rest (P.force i true)
    else 1

theorem taskStarts_le_overflow (B : ℕ) (order : List (Fin n)) (P : MaskRestriction n) :
    D.taskStarts B order P ≤ 1 + 2 * D.overflowCount B order P := by
  induction order generalizing P with
  | nil => simp [taskStarts, overflowCount]
  | cons i order ih =>
    simp only [taskStarts, overflowCount]
    split
    · change 1 + D.taskStarts B order (P.force i false) +
          D.taskStarts B order (P.force i true) ≤
        1 + 2 * (1 + D.overflowCount B order (P.force i false) +
          D.overflowCount B order (P.force i true))
      have h0 := ih (P.force i false)
      have h1 := ih (P.force i true)
      omega
    · omega

theorem entryUniverse_force_card_add (P : MaskRestriction n)
    (hd : ∀ i j, i ≠ j → Disjoint (D.leaves i).top (D.leaves j).top)
    (i : Fin n) (hi : i ∈ RepresentationUniverse.topDomain D.leaves) :
    ({ D with maskRestriction := P.force i false }).entryUniverse.card +
      ({ D with maskRestriction := P.force i true }).entryUniverse.card =
        ({ D with maskRestriction := P }).entryUniverse.card := by
  classical
  rw [D.entryUniverse_force P hd i hi false, D.entryUniverse_force P hd i hi true]
  have h := Finset.card_filter_add_card_filter_not
    (s := ({ D with maskRestriction := P }).entryUniverse) (p := fun e => i ∈ e.mask)
  simpa only [decide_eq_false_iff_not, decide_eq_true_eq, add_comm] using h

theorem overflowCount_capacity (B : ℕ)
    (hd : ∀ i j, i ≠ j → Disjoint (D.leaves i).top (D.leaves j).top)
    (hbounded : ∀ P, ∀ e ∈ ({ D with maskRestriction := P }).rawEntries,
      WeightEncoding.BoundedWeight D.input e.value)
    (order : List (Fin n)) (horder : ∀ i ∈ order, i ∈ RepresentationUniverse.topDomain D.leaves)
    (P : MaskRestriction n) :
    D.capacity * D.overflowCount B order P ≤
      (order.length + 1) * ({ D with maskRestriction := P }).entryUniverse.card := by
  induction order generalizing P with
  | nil =>
    simp only [overflowCount, List.length_nil]
    split
    · rename_i ho
      have hc : D.capacity < ({ D with maskRestriction := P }).entryUniverse.card :=
        (({ D with maskRestriction := P }).collect_overflow_iff_card B (hbounded P)).mp ho
      simp only [Nat.zero_add, one_mul, mul_one]
      omega
    · simp
  | cons i order ih =>
    simp only [overflowCount, List.length_cons]
    split
    · rename_i ho
      have hc : D.capacity < ({ D with maskRestriction := P }).entryUniverse.card :=
        (({ D with maskRestriction := P }).collect_overflow_iff_card B (hbounded P)).mp ho
      have h0 := ih (fun j hj => horder j (by simp [hj])) (P.force i false)
      have h1 := ih (fun j hj => horder j (by simp [hj])) (P.force i true)
      have hs := D.entryUniverse_force_card_add P hd i (horder i (by simp))
      generalize ({ D with maskRestriction := P }).entryUniverse.card = U at hc hs ⊢
      generalize ({ D with maskRestriction := P.force i false }).entryUniverse.card = U0 at h0 hs
      generalize ({ D with maskRestriction := P.force i true }).entryUniverse.card = U1 at h1 hs
      nlinarith only [hc, h0, h1, hs]
    · simp

theorem taskStarts_capacity (B : ℕ)
    (hd : ∀ i j, i ≠ j → Disjoint (D.leaves i).top (D.leaves j).top)
    (hbounded : ∀ P, ∀ e ∈ ({ D with maskRestriction := P }).rawEntries,
      WeightEncoding.BoundedWeight D.input e.value)
    (order : List (Fin n)) (horder : ∀ i ∈ order, i ∈ RepresentationUniverse.topDomain D.leaves)
    (P : MaskRestriction n) :
    D.capacity * D.taskStarts B order P ≤ D.capacity +
      2 * (order.length + 1) * ({ D with maskRestriction := P }).entryUniverse.card := by
  have ht := D.taskStarts_le_overflow B order P
  have ho := D.overflowCount_capacity B hd hbounded order horder P
  nlinarith

theorem completedArrays_length_le (B : ℕ) (order : List (Fin n)) (P : MaskRestriction n) :
    (D.completedArrays B order P).length ≤ D.taskStarts B order P := by
  induction order generalizing P with
  | nil =>
    simp only [completedArrays, taskStarts]
    split <;> simp
  | cons i order ih =>
    simp only [completedArrays, taskStarts]
    split
    · change (D.completedArrays B order (P.force i false) ++
          D.completedArrays B order (P.force i true)).length ≤
        1 + D.taskStarts B order (P.force i false) + D.taskStarts B order (P.force i true)
      simp only [List.length_append]
      have h0 := ih (P.force i false)
      have h1 := ih (P.force i true)
      omega
    · simp

theorem completedArrays_size_sum_le (B : ℕ)
    (hd : ∀ i j, i ≠ j → Disjoint (D.leaves i).top (D.leaves j).top)
    (hbounded : ∀ P, ∀ e ∈ ({ D with maskRestriction := P }).rawEntries,
      WeightEncoding.BoundedWeight D.input e.value)
    (order : List (Fin n)) (horder : ∀ i ∈ order, i ∈ RepresentationUniverse.topDomain D.leaves)
    (P : MaskRestriction n) :
    ((D.completedArrays B order P).map Array.size).sum ≤
      ({ D with maskRestriction := P }).entryUniverse.card := by
  induction order generalizing P with
  | nil =>
    simp only [completedArrays]
    split
    · simp
    · rename_i hc
      have hclear := Bool.eq_false_iff.mpr hc
      simpa only [List.map_singleton, List.sum_singleton, entries] using
        (({ D with maskRestriction := P }).completed_size_eq_card B (hbounded P) hclear).le
  | cons i order ih =>
    simp only [completedArrays]
    split
    · simp only [List.map_append, List.sum_append]
      have h0 := ih (fun j hj => horder j (by simp [hj])) (P.force i false)
      have h1 := ih (fun j hj => horder j (by simp [hj])) (P.force i true)
      have hs := D.entryUniverse_force_card_add P hd i (horder i (by simp))
      omega
    · rename_i hc
      have hclear := Bool.eq_false_iff.mpr hc
      simpa only [List.map_singleton, List.sum_singleton, entries] using
        (({ D with maskRestriction := P }).completed_size_eq_card B (hbounded P) hclear).le

private theorem input_sum (L : ℕ) (arrays : List (Array (Entry (Fin n)))) :
    (arrays.map (fun a => L + a.size)).sum = (arrays.map Array.size).sum + L * arrays.length := by
  induction arrays with
  | nil => simp
  | cons a arrays ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.mul_add, Nat.mul_one]
    omega

/-- Includes every reuse of the retained left array at a completed right
prefix; it is the actual check list's input-occurrence bound. -/
theorem completed_check_inputs_le (B L : ℕ) (hL : L ≤ D.capacity)
    (hd : ∀ i j, i ≠ j → Disjoint (D.leaves i).top (D.leaves j).top)
    (hbounded : ∀ P, ∀ e ∈ ({ D with maskRestriction := P }).rawEntries,
      WeightEncoding.BoundedWeight D.input e.value)
    (order : List (Fin n)) (horder : ∀ i ∈ order, i ∈ RepresentationUniverse.topDomain D.leaves)
    (P : MaskRestriction n) :
    ((D.completedArrays B order P).map (fun a => L + a.size)).sum ≤
      L + (2 * order.length + 3) * ({ D with maskRestriction := P }).entryUniverse.card := by
  rw [input_sum]
  have hn := D.completedArrays_length_le B order P
  have he := D.completedArrays_size_sum_le B hd hbounded order horder P
  have ht := D.taskStarts_le_overflow B order P
  have ho := D.overflowCount_capacity B hd hbounded order horder P
  have hscale := Nat.mul_le_mul_left (D.overflowCount B order P) hL
  nlinarith

end LowSpaceSubsetSum.RepresentationParentData

end

end OAI
