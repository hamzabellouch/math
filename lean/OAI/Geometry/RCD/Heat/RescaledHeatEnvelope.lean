import OAI.Geometry.RCD.Heat.FinitePrefixEnvelope

namespace OAI

/-! # Normalizing a finite initial contribution without changing absorption -/

open scoped BigOperators InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Dividing both mass forms by the finite background constant restores
the normalized envelope used in the cumulative theorem. -/
theorem rescaled_heat_envelope (N F : ℕ → E →L[ℝ] E)
    {b β : ℝ} (hb : 0 < b)
    (henv : ∀ i v, ⟪v, F i v⟫_ℝ ≤ b * β ^ i * ‖v‖ ^ 2 +
      ∑ j ∈ Finset.range (i + 1), β ^ (i - j) * ⟪v, N j v⟫_ℝ)
    (i : ℕ) (v : E) :
    ⟪v, (b⁻¹ • F i) v⟫_ℝ ≤ β ^ i * ‖v‖ ^ 2 +
      ∑ j ∈ Finset.range (i + 1), β ^ (i - j) * ⟪v, (b⁻¹ • N j) v⟫_ℝ := by
  have h := mul_le_mul_of_nonneg_left (henv i v) (inv_pos.mpr hb).le
  have he : b⁻¹ * (b * β ^ i * ‖v‖ ^ 2 +
      ∑ j ∈ Finset.range (i + 1), β ^ (i - j) * ⟪v, N j v⟫_ℝ) =
      β ^ i * ‖v‖ ^ 2 + ∑ j ∈ Finset.range (i + 1), β ^ (i - j) *
        (b⁻¹ * ⟪v, N j v⟫_ℝ) := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    · field_simp
    · apply Finset.sum_congr rfl
      intro j _
      ring
  rw [he] at h
  simpa only [smul_apply, inner_smul_right] using h

/-- The paired rescaling of the envelope and its mass forms keeps both
decrement inequalities, at the common constant b*C. -/
theorem rescaled_heat_decrements (N F D : E →L[ℝ] E)
    {b C : ℝ} (hb : 1 ≤ b) (hC : 0 ≤ C)
    (hD : ∀ v, 0 ≤ ⟪v, D v⟫_ℝ)
    (hlower : ∀ v, ⟪v, N v⟫_ℝ ≤ C * ⟪v, D v⟫_ℝ)
    (hupper : ∀ v, ⟪v, D v⟫_ℝ ≤ C * ⟪v, F v⟫_ℝ) (v : E) :
    ⟪v, (b⁻¹ • N) v⟫_ℝ ≤ (b * C) * ⟪v, D v⟫_ℝ ∧
      ⟪v, D v⟫_ℝ ≤ (b * C) * ⟪v, (b⁻¹ • F) v⟫_ℝ := by
  have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hinv : b⁻¹ ≤ b := (inv_le_one_of_one_le₀ hb).trans hb
  simp only [smul_apply, inner_smul_right]
  constructor
  · have h := mul_le_mul_of_nonneg_left (hlower v) (inv_pos.mpr hbpos).le
    have hc := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hinv hC) (hD v)
    nlinarith only [h, hc]
  · convert hupper v using 1
    field_simp

/-- The smallness constant scales reciprocally to the decrement constant,
so the absorption condition is unchanged by the finite background. -/
theorem rescaled_absorption_identity {b : ℝ} (hb : 0 < b) (C W ε : ℝ) :
    2 * (b * C) * W * (b⁻¹ * ε) = 2 * C * W * ε := by
  field_simp

end RegularPointCoordinates

end

end OAI
