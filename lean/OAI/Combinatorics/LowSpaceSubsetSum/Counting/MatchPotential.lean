import OAI.Combinatorics.LowSpaceSubsetSum.Streams.TieGroup

namespace OAI

/-!
# Potential matching occurrences in sorted streams

This count uses list occurrences, so repeated values and equal records are
counted separately. Removing a completed equal-key group subtracts its full
Cartesian product; this is the potential used to charge stopped replays.
-/

namespace LowSpaceSubsetSum
namespace MatchPotential

variable {α β : Type*}

def count (key₁ : α → ℤ) (key₂ : β → ℤ) : List α → List β → ℕ
  | [], _ => 0
  | x :: xs, ys => (ys.filter (fun y => decide (key₁ x = key₂ y))).length + count key₁ key₂ xs ys

theorem positive_iff (key₁ : α → ℤ) (key₂ : β → ℤ) (xs : List α) (ys : List β) :
    0 < count key₁ key₂ xs ys ↔ ∃ x ∈ xs, ∃ y ∈ ys, key₁ x = key₂ y := by
  induction xs with
  | nil => simp [count]
  | cons x xs ih =>
    have hf : 0 < (ys.filter (fun y => decide (key₁ x = key₂ y))).length ↔
        ∃ y ∈ ys, key₁ x = key₂ y := by
      simp only [List.length_pos_iff_exists_mem, List.mem_filter, decide_eq_true_eq]
    rw [count, Nat.add_pos_iff_pos_or_pos, hf, ih]
    constructor
    · rintro (⟨y, hy, heq⟩ | ⟨a, ha, b, hb, heq⟩)
      · exact ⟨x, by simp, y, hy, heq⟩
      · exact ⟨a, by simp [ha], b, hb, heq⟩
    · rintro ⟨a, ha, b, hb, heq⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Or.inl ⟨b, hb, heq⟩
      · exact Or.inr ⟨a, ha, b, hb, heq⟩

theorem append_left (key₁ : α → ℤ) (key₂ : β → ℤ) (xs zs : List α) (ys : List β) :
    count key₁ key₂ (xs ++ zs) ys = count key₁ key₂ xs ys + count key₁ key₂ zs ys := by
  induction xs with
  | nil => simp [count]
  | cons x xs ih => simp [count, ih, Nat.add_assoc]

theorem append_right (key₁ : α → ℤ) (key₂ : β → ℤ) (xs : List α) (ys zs : List β) :
    count key₁ key₂ xs (ys ++ zs) = count key₁ key₂ xs ys + count key₁ key₂ xs zs := by
  induction xs with
  | nil => simp [count]
  | cons x xs ih => simp only [count, List.filter_append, List.length_append, ih]; omega

theorem eq_zero (key₁ : α → ℤ) (key₂ : β → ℤ) (xs : List α) (ys : List β)
    (h : ∀ x ∈ xs, ∀ y ∈ ys, key₁ x ≠ key₂ y) : count key₁ key₂ xs ys = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : ys.filter (fun y => decide (key₁ x = key₂ y)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro y hy
      simpa only [decide_eq_true_eq] using h x (by simp) y hy
    rw [count, hx, List.length_nil, Nat.zero_add]
    exact ih (fun z hz => h z (by simp [hz]))

theorem eq_product (key₁ : α → ℤ) (key₂ : β → ℤ) (K : ℤ)
    (xs : List α) (ys : List β) (hx : ∀ x ∈ xs, key₁ x = K)
    (hy : ∀ y ∈ ys, key₂ y = K) : count key₁ key₂ xs ys = xs.length * ys.length := by
  induction xs with
  | nil => simp [count]
  | cons x xs ih =>
    have hxK := hx x (by simp)
    have he : ys.filter (fun y => decide (key₁ x = key₂ y)) = ys := by
      apply List.filter_eq_self.mpr
      intro y hmem
      simp only [hxK, hy y hmem, decide_true]
    rw [count, he, ih (fun z hz => hx z (by simp [hz])), List.length_cons]
    ring

theorem split_groups (key₁ : α → ℤ) (key₂ : β → ℤ) (K : ℤ)
    (xs rest₁ : List α) (ys rest₂ : List β)
    (hx : ∀ x ∈ xs, key₁ x = K) (hy : ∀ y ∈ ys, key₂ y = K)
    (hr₁ : ∀ x ∈ rest₁, key₁ x ≠ K) (hr₂ : ∀ y ∈ rest₂, key₂ y ≠ K) :
    count key₁ key₂ (xs ++ rest₁) (ys ++ rest₂) =
      xs.length * ys.length + count key₁ key₂ rest₁ rest₂ := by
  rw [append_left, append_right, append_right, eq_product key₁ key₂ K xs ys hx hy]
  have hz₁ : count key₁ key₂ xs rest₂ = 0 := eq_zero key₁ key₂ xs rest₂ (by
    intro x hxm y hym
    rw [hx x hxm]
    exact (hr₂ y hym).symm)
  have hz₂ : count key₁ key₂ rest₁ ys = 0 := eq_zero key₁ key₂ rest₁ ys (by
    intro x hxm y hym
    rw [hy y hym]
    exact hr₁ x hxm)
  simp only [hz₁, hz₂, Nat.add_zero, Nat.zero_add]

theorem sorted_dropWhile_avoids {γ : Type*} (key : γ → ℤ) (K : ℤ) (xs : List γ)
    (hsort : xs.Pairwise (fun x y => key x ≤ key y))
    (hlower : ∀ x ∈ xs, K ≤ key x) :
    ∀ x ∈ xs.dropWhile (fun x => decide (key x = K)), key x ≠ K := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hsort
    by_cases hx : key x = K
    · simpa only [List.dropWhile, hx, decide_true, ↓reduceIte] using
        ih htail (fun y hy => hlower y (by simp [hy]))
    · have hxlow := hlower x (by simp)
      simp only [List.dropWhile, hx, decide_false]
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · have hxy := hhead y hy
        omega

theorem remaining_eq_dropWhile {γ : Type*} (p : γ → Bool) (xs rest : List γ)
    (h : xs = xs.takeWhile p ++ rest) : rest = xs.dropWhile p := by
  apply List.append_cancel_left
  exact h.symm.trans List.takeWhile_append_dropWhile.symm

theorem remaining_sublist {γ : Type*} (p : γ → Bool) (xs rest : List γ)
    (h : xs = xs.takeWhile p ++ rest) : rest.Sublist xs := by
  rw [remaining_eq_dropWhile p xs rest h]
  exact List.dropWhile_sublist p

theorem remaining_avoids {γ : Type*} (key : γ → ℤ) (K : ℤ) (xs rest : List γ)
    (h : xs = xs.takeWhile (fun x => decide (key x = K)) ++ rest)
    (hsort : xs.Pairwise (fun x y => key x ≤ key y))
    (hlower : ∀ x ∈ xs, K ≤ key x) : ∀ x ∈ rest, key x ≠ K := by
  rw [remaining_eq_dropWhile _ xs rest h]
  exact sorted_dropWhile_avoids key K xs hsort hlower

theorem lower_bound_head {γ : Type*} (key : γ → ℤ) (x : γ) (xs : List γ)
    (hsort : (x :: xs).Pairwise (fun x y => key x ≤ key y)) :
    ∀ y ∈ x :: xs, key x ≤ key y := by
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · rfl
  · exact (List.pairwise_cons.mp hsort).1 y hy

theorem skip_left (key₁ : α → ℤ) (key₂ : β → ℤ) (x : α) (xs : List α) (ys : List β)
    (h : ∀ y ∈ ys, key₁ x < key₂ y) :
    count key₁ key₂ (x :: xs) ys = count key₁ key₂ xs ys := by
  have he : ys.filter (fun y => decide (key₁ x = key₂ y)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro y hy
    simpa only [decide_eq_true_eq] using (h y hy).ne
  simp only [count, he, List.length_nil, Nat.zero_add]

theorem skip_right (key₁ : α → ℤ) (key₂ : β → ℤ) (xs : List α) (y : β) (ys : List β)
    (h : ∀ x ∈ xs, key₂ y < key₁ x) :
    count key₁ key₂ xs (y :: ys) = count key₁ key₂ xs ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have he : key₁ x ≠ key₂ y := (h x (by simp)).ne.symm
    simp only [count, List.filter_cons, he, decide_false, Bool.false_eq_true, ite_false]
    rw [ih (fun z hz => h z (by simp [hz]))]

end MatchPotential
end LowSpaceSubsetSum

end OAI
