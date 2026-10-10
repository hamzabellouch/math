import Mathlib

namespace OAI

noncomputable section

open Set MeasureTheory

namespace Problem310Support

/-- Iterating a period-one membership equivalence. -/
theorem periodic_mem_nat {H : Set ℝ}
    (hH : ∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) (n : ℕ) (x : ℝ) :
    x + (n : ℝ) ∈ H ↔ x ∈ H := by
  induction n with
  | zero => simp
  | succ n ih =>
    simpa only [Nat.cast_add, Nat.cast_one, ← add_assoc] using
      (hH (x + (n : ℝ))).trans ih

/-- Integer translates of a unit cell have the same occupied volume. -/
theorem periodic_unit_volume_nat {H : Set ℝ}
    (hH : ∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) (n : ℕ) :
    volume (H ∩ Icc (n : ℝ) ((n : ℝ) + 1)) =
      volume (H ∩ Icc (0 : ℝ) 1) := by
  have hset : (fun x : ℝ => x + (n : ℝ)) ⁻¹'
      (H ∩ Icc (n : ℝ) ((n : ℝ) + 1)) = H ∩ Icc (0 : ℝ) 1 := by
    ext x
    simp only [mem_preimage, mem_inter_iff, mem_Icc, periodic_mem_nat hH]
    constructor
    · rintro ⟨hx, h₀, h₁⟩
      exact ⟨hx, by linarith, by linarith⟩
    · rintro ⟨hx, h₀, h₁⟩
      exact ⟨hx, by linarith, by linarith⟩
  simpa only [hset] using
    (measure_preimage_add_right volume (n : ℝ)
      (H ∩ Icc (n : ℝ) ((n : ℝ) + 1))).symm

/-- A period-one set occupies at most `n` times its unit-cell volume in `n` cells.
No measurability assumption is needed for this upper bound. -/
theorem periodic_nat_interval_volume_le {H : Set ℝ}
    (hH : ∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) (n : ℕ) :
    volume (H ∩ Icc (0 : ℝ) (n : ℝ)) ≤
      (n : ENNReal) * volume (H ∩ Icc (0 : ℝ) 1) := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, Icc_self, zero_mul, nonpos_iff_eq_zero]
    exact measure_mono_null inter_subset_right (measure_singleton 0)
  | succ n ih =>
    have hsplit : H ∩ Icc (0 : ℝ) ((n : ℝ) + 1) =
        (H ∩ Icc (0 : ℝ) (n : ℝ)) ∪
          (H ∩ Icc (n : ℝ) ((n : ℝ) + 1)) := by
      rw [← inter_union_distrib_left,
        Icc_union_Icc_eq_Icc (by positivity : (0 : ℝ) ≤ n) (by linarith)]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [hsplit, add_mul, one_mul]
    exact (measure_union_le _ _).trans
      (add_le_add ih (le_of_eq (periodic_unit_volume_nat hH n)))

/-- Pulling a period-one set back by a positive integer dilation cannot
increase the volume occupied inside the unit interval. -/
theorem periodic_dilate_unit_volume_le {H : Set ℝ}
    (hH : ∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) {n : ℕ} (hn : 0 < n) :
    volume ({x : ℝ | (n : ℝ) * x ∈ H} ∩ Icc (0 : ℝ) 1) ≤
      volume (H ∩ Icc (0 : ℝ) 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hset : {x : ℝ | (n : ℝ) * x ∈ H} ∩ Icc (0 : ℝ) 1 =
      (fun x : ℝ => (n : ℝ) * x) ⁻¹' (H ∩ Icc (0 : ℝ) (n : ℝ)) := by
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc, mem_preimage]
    constructor
    · rintro ⟨hx, h₀, h₁⟩
      exact ⟨hx, mul_nonneg hnR.le h₀, by nlinarith⟩
    · rintro ⟨hx, h₀, h₁⟩
      exact ⟨hx, by nlinarith, by nlinarith⟩
  rw [hset, Real.volume_preimage_mul_left hnR.ne', abs_of_pos (inv_pos.mpr hnR)]
  have hbound := mul_le_mul_right (periodic_nat_interval_volume_le hH n)
    (ENNReal.ofReal ((n : ℝ)⁻¹))
  refine hbound.trans_eq ?_
  rw [ENNReal.ofReal_inv_of_pos hnR, ENNReal.ofReal_natCast, ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (by simp), one_mul]

/-- Reflection preserves period-one membership. -/
theorem periodic_reflect {H : Set ℝ}
    (hH : ∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) :
    ∀ x : ℝ, x + 1 ∈ {y : ℝ | -y ∈ H} ↔ x ∈ {y : ℝ | -y ∈ H} := by
  intro x
  change -(x + 1) ∈ H ↔ -x ∈ H
  have heq : -(x + 1) + 1 = -x := by ring
  simpa only [heq] using (hH (-(x + 1))).symm

/-- Reflection preserves the occupied volume in a unit period. -/
theorem periodic_reflect_unit_volume {H : Set ℝ}
    (hH : ∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) :
    volume ({x : ℝ | -x ∈ H} ∩ Icc (0 : ℝ) 1) =
      volume (H ∩ Icc (0 : ℝ) 1) := by
  have hset : {x : ℝ | -x ∈ H} ∩ Icc (0 : ℝ) 1 =
      (fun x : ℝ => -x) ⁻¹' ((fun y : ℝ => 1 + y) ⁻¹'
        (H ∩ Icc (0 : ℝ) 1)) := by
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc, mem_preimage]
    have hmem : 1 + -x ∈ H ↔ -x ∈ H := by simpa only [add_comm] using hH (-x)
    rw [hmem]
    constructor
    · rintro ⟨hx, h₀, h₁⟩
      exact ⟨hx, by linarith, by linarith⟩
    · rintro ⟨hx, h₀, h₁⟩
      exact ⟨hx, by linarith, by linarith⟩
  rw [hset, Measure.measure_preimage_neg, measure_preimage_add]

/-- The reflected version of the integer-dilation volume estimate. -/
theorem periodic_neg_dilate_unit_volume_le {H : Set ℝ}
    (hH : ∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) {n : ℕ} (hn : 0 < n) :
    volume ({x : ℝ | -((n : ℝ) * x) ∈ H} ∩ Icc (0 : ℝ) 1) ≤
      volume (H ∩ Icc (0 : ℝ) 1) := by
  exact (periodic_dilate_unit_volume_le (periodic_reflect hH) hn).trans_eq
    (periodic_reflect_unit_volume hH)

end Problem310Support

end

end OAI
