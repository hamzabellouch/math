import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSecondScale

namespace OAI

/-! # One pair-independent Poisson cutoff on a dyadic block -/

namespace Ostmann

noncomputable def quadraticSecondLower (X₀ J : ℝ) : ℝ := X₀ / (2 * J)
noncomputable def quadraticSecondUpper (X₀ J : ℝ) : ℝ := 2 * X₀ * J
noncomputable def quadraticSecondWindow (J : ℝ) : ℕ := ⌈16 * J ^ 2⌉₊

theorem quadratic_second_cutoffs {X₀ X J : ℝ}
    (hX₀ : 0 < X₀) (hJ : 1 ≤ J) (hlo : X₀ / 2 ≤ X) (hhi : X ≤ 2 * X₀) :
    0 < quadraticSecondLower X₀ J ∧ 0 < quadraticSecondUpper X₀ J ∧
      quadraticSecondLower X₀ J * J ≤ X ∧
      X * J ≤ quadraticSecondUpper X₀ J ∧
      (quadraticSecondUpper X₀ J / X) ^ 2 ≤ (quadraticSecondWindow J : ℝ) + 1 := by
  have hJ₀ : 0 < J := lt_of_lt_of_le zero_lt_one hJ
  have hX : 0 < X := (half_pos hX₀).trans_le hlo
  have hlow : quadraticSecondLower X₀ J * J = X₀ / 2 := by
    unfold quadraticSecondLower
    field_simp
  have hratio : quadraticSecondUpper X₀ J / X ≤ 4 * J := by
    rw [div_le_iff₀ hX]
    unfold quadraticSecondUpper
    nlinarith [mul_le_mul_of_nonneg_right hlo hJ₀.le]
  refine ⟨by unfold quadraticSecondLower; positivity,
    by unfold quadraticSecondUpper; positivity, hlow ▸ hlo,
    mul_le_mul_of_nonneg_right hhi hJ₀.le, ?_⟩
  have hs : (quadraticSecondUpper X₀ J / X) ^ 2 ≤ (4 * J) ^ 2 :=
    (sq_le_sq₀ (by unfold quadraticSecondUpper; positivity) (by positivity)).mpr hratio
  have hc : 16 * J ^ 2 ≤ (quadraticSecondWindow J : ℝ) := Nat.le_ceil _
  nlinarith

end Ostmann

end OAI
