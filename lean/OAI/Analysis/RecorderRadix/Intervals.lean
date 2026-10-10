import Mathlib

namespace OAI

/-! Odd radix digits and separated one-letter and two-letter intervals. -/

namespace Solenoidal
namespace Radix
def base (m : ℕ) : ℝ := 2 * ((m : ℝ) + 1) + 1

def digit {m : ℕ} (a : Fin (m + 1)) : ℝ := 2 * (a.val : ℝ) + 1

noncomputable def pushDigit {m : ℕ} (a : Fin (m + 1)) (v : ℝ) : ℝ :=
  (digit a + v) / base m

def pop {m : ℕ} (a : Fin (m + 1)) (v : ℝ) : ℝ := base m * v - digit a

def first {m : ℕ} (a : Fin (m + 1)) : Set ℝ :=
  Set.Icc (pushDigit a 0) (pushDigit a 1)

def two {m : ℕ} (a b : Fin (m + 1)) : Set ℝ :=
  Set.Icc (pushDigit a (pushDigit b 0)) (pushDigit a (pushDigit b 1))

theorem base_three_le (m : ℕ) : 3 ≤ base m := by
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  dsimp [base]
  linarith

theorem base_pos (m : ℕ) : 0 < base m := lt_of_lt_of_le (by norm_num) (base_three_le m)

theorem digit_bounds {m : ℕ} (a : Fin (m + 1)) : 1 ≤ digit a ∧ digit a ≤ base m - 2 := by
  have h₀ : (0 : ℝ) ≤ a.val := Nat.cast_nonneg _
  have h₁ : (a.val : ℝ) ≤ m := by exact_mod_cast Nat.le_of_lt_succ a.isLt
  dsimp [digit, base]
  constructor <;> linarith

@[simp] theorem pop_prefix {m : ℕ} (a : Fin (m + 1)) (v : ℝ) : pop a (pushDigit a v) = v := by
  dsimp [pop, pushDigit]
  field_simp [(base_pos m).ne']
  ring

@[simp] theorem prefix_pop {m : ℕ} (a : Fin (m + 1)) (v : ℝ) : pushDigit a (pop a v) = v := by
  dsimp [pop, pushDigit]
  field_simp [(base_pos m).ne']
  ring

theorem prefix_le_prefix_iff {m : ℕ} (a : Fin (m + 1)) {u v : ℝ} :
    pushDigit a u ≤ pushDigit a v ↔ u ≤ v := by
  simp only [pushDigit, div_le_div_iff_of_pos_right (base_pos m), add_le_add_iff_left]

 
theorem prefix_image_Icc {m : ℕ} (a : Fin (m + 1)) (u v : ℝ) :
    pushDigit a '' Set.Icc u v = Set.Icc (pushDigit a u) (pushDigit a v) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(prefix_le_prefix_iff a).mpr hx.1, (prefix_le_prefix_iff a).mpr hx.2⟩
  · intro hy
    refine ⟨pop a y, ?_, prefix_pop a y⟩
    constructor
    · apply (prefix_le_prefix_iff a).mp
      simpa using hy.1
    · apply (prefix_le_prefix_iff a).mp
      simpa using hy.2

@[simp] theorem prefix_image_unit {m : ℕ} (a : Fin (m + 1)) :
    pushDigit a '' Set.Icc 0 1 = first a := prefix_image_Icc a 0 1

@[simp] theorem prefix_image_first {m : ℕ} (a b : Fin (m + 1)) :
    pushDigit a '' first b = two a b := prefix_image_Icc a _ _

@[simp] theorem pop_image_first {m : ℕ} (a : Fin (m + 1)) :
    pop a '' first a = Set.Icc 0 1 := by
  rw [← prefix_image_unit a, Set.image_image]
  simp

theorem lower_nonneg {m : ℕ} (a : Fin (m + 1)) : 0 ≤ pushDigit a 0 := by
  exact div_nonneg (by have := (digit_bounds a).1; simpa using le_trans (by norm_num) this)
    (base_pos m).le

theorem upper_le_one {m : ℕ} (a : Fin (m + 1)) : pushDigit a 1 ≤ 1 := by
  apply (div_le_one (base_pos m)).mpr
  have := (digit_bounds a).2
  linarith

 
theorem first_ordered_gap {m : ℕ} {a b : Fin (m + 1)} (hab : a.val < b.val) :
    pushDigit a 1 + 1 / base m ≤ pushDigit b 0 := by
  dsimp [pushDigit]
  rw [← add_div]
  apply (div_le_div_iff_of_pos_right (base_pos m)).mpr
  have hab' : (a.val : ℝ) + 1 ≤ b.val := by exact_mod_cast hab
  dsimp [digit]
  linarith

theorem first_separated {m : ℕ} {a b : Fin (m + 1)} (hab : a ≠ b) :
    pushDigit a 1 + 1 / base m ≤ pushDigit b 0 ∨
    pushDigit b 1 + 1 / base m ≤ pushDigit a 0 := by
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · exact Or.inl (first_ordered_gap h)
  · exact Or.inr (first_ordered_gap h)

theorem prefix_gap {m : ℕ} (a : Fin (m + 1)) {x y δ : ℝ} (h : x + δ ≤ y) :
    pushDigit a x + δ / base m ≤ pushDigit a y := by
  dsimp [pushDigit]
  rw [← add_div]
  apply (div_le_div_iff_of_pos_right (base_pos m)).mpr
  linarith

theorem two_gap_same {m : ℕ} (a : Fin (m + 1)) {b d : Fin (m + 1)} (hbd : b.val < d.val) :
    pushDigit a (pushDigit b 1) + 1 / (base m) ^ 2 ≤ pushDigit a (pushDigit d 0) := by
  simpa only [div_div, pow_two] using prefix_gap a (first_ordered_gap hbd)

theorem two_gap_first {m : ℕ} {a b c d : Fin (m + 1)} (hac : a.val < c.val) :
    pushDigit a (pushDigit b 1) + 1 / (base m) ^ 2 ≤ pushDigit c (pushDigit d 0) := by
  have h₁ := (prefix_le_prefix_iff a).mpr (upper_le_one b)
  have h₂ := (prefix_le_prefix_iff c).mpr (lower_nonneg d)
  have hg := first_ordered_gap hac
  have hb : base m ≤ (base m) ^ 2 := by
    have := base_three_le m
    nlinarith
  have hi : 1 / (base m) ^ 2 ≤ 1 / base m := one_div_le_one_div_of_le (base_pos m) hb
  linarith

 
theorem two_separated {m : ℕ} {a b c d : Fin (m + 1)} (h : (a, b) ≠ (c, d)) :
    pushDigit a (pushDigit b 1) + 1 / (base m) ^ 2 ≤ pushDigit c (pushDigit d 0) ∨
    pushDigit c (pushDigit d 1) + 1 / (base m) ^ 2 ≤ pushDigit a (pushDigit b 0) := by
  by_cases hac : a = c
  · subst c
    have hbd : b.val ≠ d.val := by
      intro hval
      exact h (Prod.ext rfl (Fin.ext hval))
    rcases lt_or_gt_of_ne hbd with hlt | hlt
    · exact Or.inl (two_gap_same a hlt)
    · exact Or.inr (two_gap_same a hlt)
  · have hne : a.val ≠ c.val := fun hval => hac (Fin.ext hval)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact Or.inl (two_gap_first hlt)
    · exact Or.inr (two_gap_first hlt)
end Radix
end Solenoidal

end OAI
