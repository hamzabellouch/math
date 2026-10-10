import OAI.Combinatorics.BinaryEdit.TaggedAlignment
import OAI.Combinatorics.BinaryEdit.TaggedArrayPrerequisites

namespace OAI

/-! Ordered-tag alignment bounds for arrays. -/
namespace TreeEdit.BinaryLower.Tagged

open scoped BigOperators
open TaggedExtraction

/-- Harmonic deficit bound for literal arrays of fixed-width, ordered-tag blocks. -/
theorem tagged_arrays_harmonic {α : Type*} {T m B : ℕ}
    (hT : 0 < T) (hm : 2 ≤ m) (hB : 0 < B)
    (X Y : Fin T → Fin m → Word α B) (tag : α → Fin m)
    (hX : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (X a i).val → tag s = i)
    (hY : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (Y a i).val → tag s = i)
    (d : ℝ) (hd : 0 ≤ d)
    (hlocal : ∀ a b, d ≤ ∑ i, (deficit B (X a i).val (Y b i).val : ℝ)) :
    (T : ℝ) * d * (((m - 1) * B : ℕ) : ℝ) /
      (d + (((m - 1) * B : ℕ) : ℝ)) ≤
        (deficit (T * m * B) (rows X) (rows Y) : ℝ) := by
  apply tagged_slice_alignment hT hm hB (rows X) (rows Y)
    (length_rows X) (length_rows Y)
  · intro p hp q hq heq
    exact equal_symbols_same_tag_of_decoder X Y tag hX hY (by omega) hB p q
      (by simpa only [length_rows] using hp)
      (by simpa only [length_rows] using hq) heq
  · exact hd
  · intro a ha b hb
    simpa only [Nat.cast_mul] using
      local_slice_capacity X Y tag hX hY hlocal ⟨a, ha⟩ ⟨b, hb⟩

/-- Both inequalities in `eq:tagged-result`, with no matching-alignment premise. -/
theorem tagged_arrays_bounds {α : Type*} {T m B : ℕ}
    (hT : 0 < T) (hm : 2 ≤ m) (hB : 0 < B)
    (X Y : Fin T → Fin m → Word α B) (tag : α → Fin m)
    (hX : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (X a i).val → tag s = i)
    (hY : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (Y a i).val → tag s = i)
    (d : ℝ) (hd : 0 ≤ d)
    (hlocal : ∀ a b, d ≤ ∑ i, (deficit B (X a i).val (Y b i).val : ℝ)) :
    ((T : ℝ) * d * (((m - 1) * B : ℕ) : ℝ) /
      (d + (((m - 1) * B : ℕ) : ℝ)) ≤
        (deficit (T * m * B) (rows X) (rows Y) : ℝ)) ∧
    ((T : ℝ) / 2 * min d (((m - 1) * B : ℕ) : ℝ) ≤
      (T : ℝ) * d * (((m - 1) * B : ℕ) : ℝ) /
        (d + (((m - 1) * B : ℕ) : ℝ))) := by
  refine ⟨tagged_arrays_harmonic hT hm hB X Y tag hX hY d hd hlocal, ?_⟩
  apply half_min_le_harmonic hd _ (Nat.cast_nonneg _)
  exact_mod_cast Nat.mul_pos (by omega : 0 < m - 1) hB

/-- The convenient `Td/2` form used in both tree separation inductions. -/
theorem tagged_arrays_half {α : Type*} {T m B : ℕ}
    (hT : 0 < T) (hm : 2 ≤ m) (hB : 0 < B)
    (X Y : Fin T → Fin m → Word α B) (tag : α → Fin m)
    (hX : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (X a i).val → tag s = i)
    (hY : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (Y a i).val → tag s = i)
    (d : ℝ) (hd : 0 ≤ d)
    (hlocal : ∀ a b, d ≤ ∑ i, (deficit B (X a i).val (Y b i).val : ℝ))
    (hdg : d ≤ (((m - 1) * B : ℕ) : ℝ)) :
    (T : ℝ) * d / 2 ≤ (deficit (T * m * B) (rows X) (rows Y) : ℝ) := by
  obtain ⟨hmain, hhalf⟩ := tagged_arrays_bounds hT hm hB X Y tag hX hY d hd hlocal
  rw [min_eq_left hdg] at hhalf
  have h := hhalf.trans hmain
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

/-- Ordered-tag alignment for pairwise disjoint alphabets.
The decoder used internally is constructed, not an additional hypothesis. -/
theorem rows_with_ordered_tags {α : Type*} {T m B : ℕ}
    (hT : 0 < T) (hm : 2 ≤ m) (hB : 0 < B)
    (Γ : Fin m → Set α) (hΓ : Pairwise fun i j => Disjoint (Γ i) (Γ j))
    (X Y : Fin T → Fin m → Word α B)
    (hX : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (X a i).val → s ∈ Γ i)
    (hY : ∀ (a : Fin T) (i : Fin m) (s : α), s ∈ (Y a i).val → s ∈ Γ i)
    (d : ℝ) (hd : 0 ≤ d)
    (hlocal : ∀ a b, d ≤ ∑ i, (deficit B (X a i).val (Y b i).val : ℝ)) :
    ((T : ℝ) * d * (((m - 1) * B : ℕ) : ℝ) /
      (d + (((m - 1) * B : ℕ) : ℝ)) ≤
        (deficit (T * m * B) (rows X) (rows Y) : ℝ)) ∧
    ((T : ℝ) / 2 * min d (((m - 1) * B : ℕ) : ℝ) ≤
      (T : ℝ) * d * (((m - 1) * B : ℕ) : ℝ) /
        (d + (((m - 1) * B : ℕ) : ℝ))) ∧
    (d ≤ (((m - 1) * B : ℕ) : ℝ) →
      (T : ℝ) * d / 2 ≤ (deficit (T * m * B) (rows X) (rows Y) : ℝ)) := by
  obtain ⟨tag, htX, htY⟩ := exists_array_decoder X Y (by omega) Γ hΓ hX hY
  obtain ⟨hh, hm'⟩ := tagged_arrays_bounds hT hm hB X Y tag htX htY d hd hlocal
  exact ⟨hh, hm', tagged_arrays_half hT hm hB X Y tag htX htY d hd hlocal⟩

end TreeEdit.BinaryLower.Tagged

end OAI
