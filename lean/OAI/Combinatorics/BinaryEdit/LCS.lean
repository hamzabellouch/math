import OAI.Combinatorics.BinaryEdit.Model
import OAI.Combinatorics.TreeEdit.Alignments
import OAI.Combinatorics.BinaryEdit.LCSCore
import Mathlib.Data.List.NodupEquivFin

namespace OAI

/-! Basic properties of the manuscript's exact longest-common-subsequence
length. All maxima are attained by actual ordered sublists. -/
noncomputable section
namespace TreeEdit.BinaryLower

universe u
variable {α : Type u}

@[simp] theorem lcs_nil_left (x : List α) : lcs [] x = 0 :=
  Nat.eq_zero_of_le_zero (lcs_le_length_left [] x)

@[simp] theorem lcs_nil_right (x : List α) : lcs x [] = 0 :=
  Nat.eq_zero_of_le_zero (lcs_le_length_right x [])

theorem lcs_mono_left {x x' y : List α} (h : x.Sublist x') :
    lcs x y ≤ lcs x' y := by
  obtain ⟨z, hx, hy, hz⟩ := exists_lcs x y
  rw [← hz]
  exact length_le_lcs (hx.trans h) hy

theorem lcs_mono_right {x y y' : List α} (h : y.Sublist y') :
    lcs x y ≤ lcs x y' := by
  obtain ⟨z, hx, hy, hz⟩ := exists_lcs x y
  rw [← hz]
  exact length_le_lcs hx (hy.trans h)

theorem lcs_eq_left_of_sublist {x y : List α} (h : x.Sublist y) :
    lcs x y = x.length :=
  Nat.le_antisymm (lcs_le_length_left x y) (length_le_lcs (.refl _) h)

theorem lcs_eq_length_iff {x y : List α} (hlen : x.length = y.length) :
    lcs x y = x.length ↔ x = y := by
  constructor
  · intro h
    obtain ⟨z, hx, hy, hz⟩ := exists_lcs x y
    have hzx : z = x := hx.eq_of_length (hz.trans h)
    subst z
    exact hy.eq_of_length hlen
  · rintro rfl
    exact lcs_self _

theorem deficit_eq_zero_iff {n : ℕ} {x y : List α}
    (hx : x.length = n) (hy : y.length = n) :
    deficit n x y = 0 ↔ x = y := by
  rw [deficit, Nat.sub_eq_zero_iff_le]
  constructor
  · intro h
    apply (lcs_eq_length_iff (hx.trans hy.symm)).mp
    have depth := lcs_le_length_left x y
    omega
  · rintro rfl
    simp [hx]

theorem one_le_deficit_of_ne {n : ℕ} {x y : List α}
    (hx : x.length = n) (hy : y.length = n) (hne : x ≠ y) :
    1 ≤ deficit n x y := by
  have h : deficit n x y ≠ 0 := fun h => hne ((deficit_eq_zero_iff hx hy).mp h)
  omega

@[simp] theorem deficit_self {n : ℕ} {x : List α} (hx : x.length = n) :
    deficit n x x = 0 := (deficit_eq_zero_iff hx hx).mpr rfl

theorem deficit_symm (n : ℕ) (x y : List α) :
    deficit n x y = deficit n y x := by
  simp only [deficit, lcs_comm x y]

/-- The overlap inequality underlying the triangle inequality for
insertion-deletion distance. -/
theorem lcs_overlap (x y z : List α) :
    lcs x y + lcs y z ≤ y.length + lcs x z := by
  obtain ⟨u, hux, huy, hu⟩ := exists_lcs x y
  obtain ⟨v, hvy, hvz, hv⟩ := exists_lcs y z
  obtain ⟨w, hwu, hwv, hw⟩ := common_sublist_lower_bound huy hvy
  have hwl := length_le_lcs (hwu.trans hux) (hwv.trans hvz)
  omega

/-- To bound the maximal matching size, it suffices to bound every common
subsequence. This also avoids any appeal to an unattained supremum. -/
theorem lcs_le_iff {x y : List α} {n : ℕ} :
    lcs x y ≤ n ↔ ∀ z : List α, z.Sublist x → z.Sublist y → z.length ≤ n := by
  constructor
  · intro h z hx hy
    exact (length_le_lcs hx hy).trans h
  · intro h
    obtain ⟨z, hx, hy, hz⟩ := exists_lcs x y
    rw [← hz]
    exact h z hx hy

/-- Concatenating two increasing matchings gives an increasing matching. -/
theorem lcs_append_ge (x₁ x₂ y₁ y₂ : List α) :
    lcs x₁ y₁ + lcs x₂ y₂ ≤ lcs (x₁ ++ x₂) (y₁ ++ y₂) := by
  obtain ⟨z₁, hx₁, hy₁, hz₁⟩ := exists_lcs x₁ y₁
  obtain ⟨z₂, hx₂, hy₂, hz₂⟩ := exists_lcs x₂ y₂
  have h := length_le_lcs (hx₁.append hx₂) (hy₁.append hy₂)
  simpa [List.length_append, hz₁, hz₂] using h

/-- Splitting the source word partitions any common subsequence. -/
theorem lcs_append_left_le (x₁ x₂ y : List α) :
    lcs (x₁ ++ x₂) y ≤ lcs x₁ y + lcs x₂ y := by
  obtain ⟨z, hx, hy, hz⟩ := exists_lcs (x₁ ++ x₂) y
  obtain ⟨z₁, z₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.mp hx
  have hz₁ := length_le_lcs h₁ ((List.sublist_append_left z₁ z₂).trans hy)
  have hz₂ := length_le_lcs h₂ ((List.sublist_append_right z₁ z₂).trans hy)
  simp only [List.length_append] at hz
  omega

theorem lcs_append_right_le (x y₁ y₂ : List α) :
    lcs x (y₁ ++ y₂) ≤ lcs x y₁ + lcs x y₂ := by
  simpa only [lcs_comm] using lcs_append_left_le y₁ y₂ x

theorem deficit_add_lcs {n : ℕ} (x y : List α) (hx : x.length = n) :
    deficit n x y + lcs x y = n := by
  have h := lcs_le_length_left x y
  simp only [deficit]
  omega

/-- Relabeling symbols cannot destroy a common subsequence. -/
theorem lcs_le_map {β : Type*} (f : α → β) (x y : List α) :
    lcs x y ≤ lcs (x.map f) (y.map f) := by
  obtain ⟨z, hx, hy, hz⟩ := exists_lcs x y
  have h := length_le_lcs (hx.map f) (hy.map f)
  simpa only [List.length_map, hz] using h

/-- Injective alphabet relabeling preserves the exact longest common
subsequence length. No nonemptiness assumption on either alphabet is needed. -/
theorem lcs_map_injective {β : Type*} (f : α → β) (hf : Function.Injective f)
    (x y : List α) : lcs (x.map f) (y.map f) = lcs x y := by
  apply Nat.le_antisymm
  · obtain ⟨z, hx, hy, hz⟩ := exists_lcs (x.map f) (y.map f)
    obtain ⟨u, hux, hzu⟩ := List.sublist_map_iff.mp hx
    obtain ⟨v, hvy, hzv⟩ := List.sublist_map_iff.mp hy
    have huv : u = v := (List.map_inj_right (fun _ _ h => hf h)).mp (hzu.symm.trans hzv)
    subst v
    have h := length_le_lcs hux hvy
    have hlen : z.length = u.length := by rw [hzu, List.length_map]
    omega
  · exact lcs_le_map f x y

theorem deficit_map_injective {β : Type*} (f : α → β) (hf : Function.Injective f)
    (n : ℕ) (x y : List α) :
    deficit n (x.map f) (y.map f) = deficit n x y := by
  simp only [deficit, lcs_map_injective f hf]

end TreeEdit.BinaryLower

end

end OAI
