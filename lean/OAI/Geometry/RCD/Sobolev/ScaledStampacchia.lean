import OAI.Geometry.RCD.Sobolev.StampacchiaBound

namespace OAI

/-! # Scale-invariant extinction of superlevel distributions -/

noncomputable section
namespace RegularPointCoordinates

/-- The exact cancellation of height and volume factors in a superlevel
recurrence. Keeping these factors is essential when the ball shrinks. -/
theorem rescaled_superlevel_coefficient {R A M H p y t : ℝ}
    (hM : 0 < M) (hH : 0 < H) (hy : 0 ≤ y) (ht : 0 < t)
    (hscale : R * M ^ (p - 2) = A * H ^ p) :
    (R * (M * y) ^ (p - 1) / (H * t) ^ p) / M =
      A * y ^ (p - 1) / t ^ p := by
  have hpM : M ^ (p - 1) = M ^ (p - 2) * M := by
    rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add hM, Real.rpow_one]
  rw [Real.mul_rpow hM.le hy, Real.mul_rpow hH.le ht.le, hpM]
  have he : R * (M ^ (p - 2) * M * y ^ (p - 1)) =
      (R * M ^ (p - 2)) * M * y ^ (p - 1) := by ring
  rw [he, hscale]
  have hHp : H ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hH _)
  have htp : t ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht _)
  field_simp

/-- A uniform extinction constant survives simultaneous rescaling of the
height and the initial volume. -/
theorem exists_scaled_extinction_level {A p : ℝ} (hA : 0 ≤ A) (hp : 2 < p) :
    ∃ K : ℝ, 0 < K ∧ ∀ (R M H : ℝ), 0 < M → 0 < H →
      R * M ^ (p - 2) = A * H ^ p → ∀ Y : ℝ → ℝ,
      (∀ k, 0 ≤ k → 0 ≤ Y k) → Y 0 ≤ M →
      (∀ k l, 0 ≤ k → k ≤ l → Y l ≤ Y k) →
      (∀ k l, 0 ≤ k → k < l → Y l ≤ R * Y k ^ (p - 1) / (l - k) ^ p) →
      Y (K * H) = 0 := by
  obtain ⟨K, hK, hExt⟩ := exists_extinction_level (M := 1) hA (by norm_num) hp
  refine ⟨K, hK, ?_⟩
  intro R M H hM hH hscale Y hY hstart hmono hstep
  let Z := fun t => Y (H * t) / M
  have hZ (t : ℝ) (ht : 0 ≤ t) : 0 ≤ Z t :=
    div_nonneg (hY _ (mul_nonneg hH.le ht)) hM.le
  have hZ0 : Z 0 ≤ 1 := by
    dsimp only [Z]
    rw [mul_zero, div_le_one hM]
    exact hstart
  have hZmono (k l : ℝ) (hk : 0 ≤ k) (hkl : k ≤ l) : Z l ≤ Z k :=
    div_le_div_of_nonneg_right (hmono _ _ (mul_nonneg hH.le hk)
      (mul_le_mul_of_nonneg_left hkl hH.le)) hM.le
  have hZstep (k l : ℝ) (hk : 0 ≤ k) (hkl : k < l) :
      Z l ≤ A * Z k ^ (p - 1) / (l - k) ^ p := by
    have hh := div_le_div_of_nonneg_right
      (hstep (H * k) (H * l) (mul_nonneg hH.le hk)
        (mul_lt_mul_of_pos_left hkl hH)) hM.le
    have hYZ : Y (H * k) = M * Z k := by dsimp only [Z]; field_simp
    rw [hYZ, ← mul_sub] at hh
    exact hh.trans_eq (rescaled_superlevel_coefficient hM hH (hZ k hk)
      (sub_pos.mpr hkl) hscale)
  have hz := hExt Z hZ hZ0 hZmono hZstep
  have hz' : Y (H * K) = 0 := (div_eq_zero_iff).mp hz |>.resolve_right (ne_of_gt hM)
  simpa only [mul_comm H K] using hz'

/-- The normalized Dirichlet Sobolev coefficient has precisely the
homogeneity required by the superlevel recurrence. -/
theorem normalized_sobolev_coefficient {C s V d : ℝ}
    (hC : 0 ≤ C) (hs : 0 < s) (hV : 0 < V) (hd : 1 < d) :
    (C * s * V ^ (1 / d - 1)) ^ (2 * d) * V ^ (2 * d - 2) =
      C ^ (2 * d) * s ^ (2 * d) := by
  have he : (1 / d - 1) * (2 * d) + (2 * d - 2) = 0 := by
    field_simp
    ring
  rw [Real.mul_rpow (mul_nonneg hC hs.le) (Real.rpow_nonneg hV.le _),
    Real.mul_rpow hC hs.le, ← Real.rpow_mul hV.le]
  calc
    _ = C ^ (2 * d) * s ^ (2 * d) *
        (V ^ ((1 / d - 1) * (2 * d)) * V ^ (2 * d - 2)) := by ring
    _ = _ := by rw [← Real.rpow_add hV, he, Real.rpow_zero, mul_one]

end RegularPointCoordinates

end

end OAI
