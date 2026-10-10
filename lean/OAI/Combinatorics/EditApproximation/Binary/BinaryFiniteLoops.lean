import OAI.Combinatorics.EditApproximation.Binary.BinaryBandEnvelope
import OAI.Combinatorics.EditApproximation.Binary.BinaryBandInputWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Executed finite filters and stored fraction reductions used by the
band tests. Callback costs and list construction are included. -/

namespace EditApproximation



theorem filterWithWork_value {α : Type*} (test : α → Bool × ℕ) (values : List α) :
    (filterWithWork test values).1 = values.filter (fun a => (test a).1) := by
  induction values with
  | nil => rfl
  | cons a rest ih =>
    simp only [filterWithWork, List.filter_cons, ih]

theorem filterWithWork_cost {α : Type*} (test : α → Bool × ℕ) (values : List α)
    (C : ℕ) (hC : ∀ a ∈ values, (test a).2 ≤ C) :
    (filterWithWork test values).2 ≤ values.length * (C + 3) := by
  induction values with
  | nil => simp [filterWithWork]
  | cons a rest ih =>
    have ha := hC a List.mem_cons_self
    have ht := ih (fun b hb => hC b (List.mem_cons_of_mem _ hb))
    change (test a).2 + (filterWithWork test rest).2 + 3 ≤ _
    simp only [List.length_cons]
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- Both branch values are visited; this makes the work count independent
of the outcome while returning the usual finite conjunction. -/


theorem allWithWork_value {α : Type*} (test : α → Bool × ℕ) (values : List α) :
    (allWithWork test values).1 = true ↔ ∀ a ∈ values, (test a).1 = true := by
  induction values with
  | nil => simp [allWithWork]
  | cons a rest ih => simp only [allWithWork, Bool.and_eq_true, ih, List.forall_mem_cons]

theorem allWithWork_cost {α : Type*} (test : α → Bool × ℕ) (values : List α)
    (C : ℕ) (hC : ∀ a ∈ values, (test a).2 ≤ C) :
    (allWithWork test values).2 ≤ values.length * (C + 3) := by
  induction values with
  | nil => simp [allWithWork]
  | cons a rest ih =>
    have ha := hC a List.mem_cons_self
    have ht := ih (fun b hb => hC b (List.mem_cons_of_mem _ hb))
    change (test a).2 + (allWithWork test rest).2 + 3 ≤ _
    simp only [List.length_cons]
    rw [Nat.add_mul, Nat.one_mul]
    omega

namespace BinaryFraction



theorem leWithWork_value (a b : BinaryFraction) :
    (a.leWithWork b).1 = true ↔ a.value ≤ b.value := by
  simp only [leWithWork, Bool.not_eq_true_eq_eq_false]
  rw [Bool.eq_false_iff]
  constructor
  · intro h
    exact le_of_not_gt (fun hlt => h ((ltWithWork_value b a).mpr hlt))
  · intro h hlt
    exact (not_lt_of_ge h) ((ltWithWork_value b a).mp hlt)

theorem leWithWork_cost (a b : BinaryFraction) (B : ℕ) (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (a.leWithWork b).2 ≤ 1000 * (B + 1) ^ 2 + 1 :=
  Nat.add_le_add_right (ltWithWork_cost b a B hb ha) 1




theorem minWithWork_value (a b : BinaryFraction) :
    (minWithWork a b).1.value = min a.value b.value := by
  by_cases h : a.value < b.value
  · simp only [minWithWork, (ltWithWork_value a b).mpr h, ↓reduceIte, min_eq_left h.le]
  · have hb : (a.ltWithWork b).1 = false :=
      Bool.eq_false_iff.mpr (fun hh => h ((ltWithWork_value a b).mp hh))
    simp only [minWithWork, hb, Bool.false_eq_true, ↓reduceIte, min_eq_right (le_of_not_gt h)]

theorem minWithWork_width (a b : BinaryFraction) :
    (minWithWork a b).1.width ≤ max a.width b.width := by
  unfold minWithWork
  dsimp only
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem minWithWork_cost (a b : BinaryFraction) (B : ℕ) (ha : a.width ≤ B) (hb : b.width ≤ B) :
    (minWithWork a b).2 ≤ 1000 * (B + 1) ^ 2 + 1 :=
  Nat.add_le_add_right (ltWithWork_cost a b B ha hb) 1



theorem minimumWithWork_value (fallback : BinaryFraction) (values : List BinaryFraction) :
    (minimumWithWork fallback values).1.value = rationalMinimum fallback.value (values.map value) := by
  induction values with
  | nil => rfl
  | cons head rest ih =>
    simp only [minimumWithWork, minWithWork_value, ih, List.map_cons, rationalMinimum]

theorem minimumWithWork_width (fallback : BinaryFraction) (values : List BinaryFraction)
    (B : ℕ) (hf : fallback.width ≤ B) (hvalues : ∀ a ∈ values, a.width ≤ B) :
    (minimumWithWork fallback values).1.width ≤ B := by
  induction values with
  | nil => exact hf
  | cons head rest ih =>
    exact (minWithWork_width head (minimumWithWork fallback rest).1).trans
      (max_le (hvalues head List.mem_cons_self) (ih (fun a ha => hvalues a (List.mem_cons_of_mem _ ha))))

theorem minimumWithWork_cost (fallback : BinaryFraction) (values : List BinaryFraction)
    (B : ℕ) (hf : fallback.width ≤ B) (hvalues : ∀ a ∈ values, a.width ≤ B) :
    (minimumWithWork fallback values).2 ≤ 1 + values.length * (1000 * (B + 1) ^ 2 + 2) := by
  induction values with
  | nil => simp [minimumWithWork]
  | cons head rest ih =>
    have htail := ih (fun a ha => hvalues a (List.mem_cons_of_mem _ ha))
    have hw := minimumWithWork_width fallback rest B hf (fun a ha => hvalues a (List.mem_cons_of_mem _ ha))
    have hc := minWithWork_cost head (minimumWithWork fallback rest).1 B
      (hvalues head List.mem_cons_self) hw
    change (minimumWithWork fallback rest).2 + (minWithWork head (minimumWithWork fallback rest).1).2 + 1 ≤ _
    simp only [List.length_cons]
    rw [Nat.add_mul, Nat.one_mul]
    omega



theorem sumListWithWork_value (values : List BinaryFraction) :
    (sumListWithWork values).1.value = (values.map value).sum := by
  rw [sumListWithWork, bandMassTotalWithWork_value]
  simp only [vector_get_ofFn]
  rw [← List.sum_ofFn, List.ofFn_comp', List.ofFn_get]

theorem sumListWithWork_width (values : List BinaryFraction) (B : ℕ)
    (hB : ∀ a ∈ values, a.width ≤ B) :
    (sumListWithWork values).1.width ≤ bandMassTotalStorageBudget values.length B := by
  exact (dotListWithWork_width_le_storageBits (Vector.ofFn values.get)
      (Vector.replicate values.length one) (List.finRange values.length)).trans
    (bandMassTotalWithWork_storage (Vector.ofFn values.get) B (by
      intro i
      rw [vector_get_ofFn]
      exact hB _ (List.get_mem _ _)))

theorem sumListWithWork_cost (values : List BinaryFraction) (B : ℕ)
    (hB : ∀ a ∈ values, a.width ≤ B) :
    (sumListWithWork values).2 ≤ storedSumBitBudget values.length B + 6 * values.length := by
  exact Nat.add_le_add_right (bandMassTotalWithWork_cost (Vector.ofFn values.get) B (by
    intro i
    rw [vector_get_ofFn]
    exact hB _ (List.get_mem _ _))) _

end BinaryFraction
end EditApproximation

end OAI
