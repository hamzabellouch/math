import OAI.GroupTheory.Thompson.BasicInterval

namespace OAI

/-!
# Nesting and normalization of basic dyadic intervals

The endpoint comparisons are made on a common dyadic grid. In particular,
intersecting open interiors force one basic interval to contain the other.
-/

noncomputable section

namespace ThompsonNonamenability.BasicInterval

open Set

/-- Express a left endpoint on any finer dyadic grid. -/
theorem left_eq_on_finer_grid (I : BasicInterval) {s : ℕ} (h : I.depth ≤ s) :
    I.left = ((I.index.val * 2 ^ (s - I.depth) : ℕ) : ℝ) / (2 : ℝ) ^ s := by
  have hp : (2 : ℝ) ^ s = (2 : ℝ) ^ I.depth * (2 : ℝ) ^ (s - I.depth) := by
    rw [← pow_add, Nat.add_sub_cancel' h]
  have hI : (2 : ℝ) ^ I.depth ≠ 0 := by positivity
  have hD : (2 : ℝ) ^ (s - I.depth) ≠ 0 := by positivity
  simp only [left, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, hp]
  field_simp [hI, hD]

/-- Express a right endpoint on any finer dyadic grid. -/
theorem right_eq_on_finer_grid (I : BasicInterval) {s : ℕ} (h : I.depth ≤ s) :
    I.right = (((I.index.val + 1) * 2 ^ (s - I.depth) : ℕ) : ℝ) /
      (2 : ℝ) ^ s := by
  have hp : (2 : ℝ) ^ s = (2 : ℝ) ^ I.depth * (2 : ℝ) ^ (s - I.depth) := by
    rw [← pow_add, Nat.add_sub_cancel' h]
  have hI : (2 : ℝ) ^ I.depth ≠ 0 := by positivity
  have hD : (2 : ℝ) ^ (s - I.depth) ≠ 0 := by positivity
  simp only [right, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow,
    Nat.cast_ofNat, hp]
  field_simp [hI, hD]

/-- A contained basic interval has at least the depth of its container. -/
theorem depth_le_of_contained {I K : BasicInterval} (h : K.Contained I) :
    I.depth ≤ K.depth := by
  have hl := length_le_of_contained h
  change ((2 : ℝ) ^ K.depth)⁻¹ ≤ ((2 : ℝ) ^ I.depth)⁻¹ at hl
  have hp : (2 : ℝ) ^ I.depth ≤ (2 : ℝ) ^ K.depth :=
    (inv_le_inv₀ (by positivity) (by positivity)).mp hl
  exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hp

/-- Containment gives the integer endpoint bounds on the finer grid. -/
theorem index_bounds_of_contained {I K : BasicInterval} (h : K.Contained I) :
    I.index.val * 2 ^ (K.depth - I.depth) ≤ K.index.val ∧
      K.index.val + 1 ≤ (I.index.val + 1) * 2 ^ (K.depth - I.depth) := by
  have hd := depth_le_of_contained h
  have hp : 0 < (2 : ℝ) ^ K.depth := by positivity
  have hl := h.1
  have hr := h.2
  rw [left_eq_on_finer_grid I hd, left] at hl
  rw [right_eq_on_finer_grid I hd, right] at hr
  constructor
  · exact_mod_cast (div_le_div_iff_of_pos_right hp).mp hl
  · exact_mod_cast (div_le_div_iff_of_pos_right hp).mp hr

/-- A subinterval is precisely the image of a basic interval under the
container's affine chart. -/
theorem contained_iff_exists_comp {I K : BasicInterval} :
    K.Contained I ↔ ∃ J : BasicInterval, I.comp J = K := by
  constructor
  · intro h
    have hd := depth_le_of_contained h
    obtain ⟨hl, hr⟩ := index_bounds_of_contained h
    have hn : K.index.val - I.index.val * 2 ^ (K.depth - I.depth) <
        2 ^ (K.depth - I.depth) := by
      rw [Nat.add_mul, Nat.one_mul] at hr
      omega
    let J : BasicInterval :=
      ⟨K.depth - I.depth, ⟨K.index.val - I.index.val * 2 ^ (K.depth - I.depth), hn⟩⟩
    refine ⟨J, ext_depth_index ?_ ?_⟩
    · change I.depth + (K.depth - I.depth) = K.depth
      omega
    · change I.index.val * 2 ^ (K.depth - I.depth) +
          (K.index.val - I.index.val * 2 ^ (K.depth - I.depth)) = K.index.val
      omega
  · rintro ⟨J, rfl⟩
    exact comp_contained I J

/-- The affine preimage of a contained basic interval is unique. -/
theorem contained_iff_exists_unique_comp {I K : BasicInterval} :
    K.Contained I ↔ ∃! J : BasicInterval, I.comp J = K := by
  constructor
  · intro h
    obtain ⟨J, hJ⟩ := contained_iff_exists_comp.mp h
    refine ⟨J, hJ, ?_⟩
    intro J' hJ'
    exact comp_injective I (hJ'.trans hJ.symm)
  · rintro ⟨J, hJ, _⟩
    exact contained_iff_exists_comp.mpr ⟨J, hJ⟩

alias containment_iff_exists_unique_comp := contained_iff_exists_unique_comp

/-- The basic interval obtained by applying the inverse chart of `I` to `K`. -/
def normalize (I K : BasicInterval) (h : K.Contained I) : BasicInterval :=
  Classical.choose (contained_iff_exists_comp.mp h)

theorem comp_normalize (I K : BasicInterval) (h : K.Contained I) :
    I.comp (normalize I K h) = K :=
  Classical.choose_spec (contained_iff_exists_comp.mp h)

@[simp] theorem normalize_comp (I J : BasicInterval) (h : (I.comp J).Contained I) :
    normalize I (I.comp J) h = J := by
  apply comp_injective I
  exact comp_normalize I (I.comp J) h

/-- At ordered depths, overlap of open interiors implies containment. -/
theorem contained_of_overlap_of_depth_le {I K : BasicInterval}
    (hd : I.depth ≤ K.depth) (h : (I.interior ∩ K.interior).Nonempty) :
    K.Contained I := by
  obtain ⟨x, hxI, hxK⟩ := h
  have hl : I.left < K.right := lt_trans hxI.1 hxK.2
  have hr : K.left < I.right := lt_trans hxK.1 hxI.2
  have hp : 0 < (2 : ℝ) ^ K.depth := by positivity
  rw [left_eq_on_finer_grid I hd, right] at hl
  rw [right_eq_on_finer_grid I hd, left] at hr
  have hln : I.index.val * 2 ^ (K.depth - I.depth) < K.index.val + 1 := by
    exact_mod_cast (div_lt_div_iff_of_pos_right hp).mp hl
  have hrn : K.index.val < (I.index.val + 1) * 2 ^ (K.depth - I.depth) := by
    exact_mod_cast (div_lt_div_iff_of_pos_right hp).mp hr
  have hl' : I.index.val * 2 ^ (K.depth - I.depth) ≤ K.index.val := by omega
  have hr' : K.index.val + 1 ≤ (I.index.val + 1) * 2 ^ (K.depth - I.depth) := by omega
  constructor
  · rw [left_eq_on_finer_grid I hd, left]
    apply (div_le_div_iff_of_pos_right hp).mpr
    exact_mod_cast hl'
  · rw [right_eq_on_finer_grid I hd, right]
    apply (div_le_div_iff_of_pos_right hp).mpr
    exact_mod_cast hr'

/-- Basic dyadic intervals with intersecting open interiors are nested. -/
theorem overlap_interior_nested {I J : BasicInterval}
    (h : (I.interior ∩ J.interior).Nonempty) : I.Contained J ∨ J.Contained I := by
  rcases le_total I.depth J.depth with hd | hd
  · exact Or.inr (contained_of_overlap_of_depth_le hd h)
  · apply Or.inl
    apply contained_of_overlap_of_depth_le hd
    simpa only [inter_comm] using h

end ThompsonNonamenability.BasicInterval

end

end OAI
