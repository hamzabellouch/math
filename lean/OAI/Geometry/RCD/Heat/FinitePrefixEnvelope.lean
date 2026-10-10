import OAI.Geometry.RCD.Heat.HeatCumulative

namespace OAI

/-! # Separating finitely many initial scales from a heat envelope -/

open scoped BigOperators InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

/-- Shifting a geometric convolution leaves a finite initial contribution
with the same geometric decay. -/
theorem geometric_envelope_shift (f : ℕ → ℝ) (β a : ℝ) (J i : ℕ) :
    β ^ (J + i) * a + ∑ j ∈ Finset.range (J + i + 1), β ^ (J + i - j) * f j =
      β ^ i * (β ^ J * a + ∑ j ∈ Finset.range J, β ^ (J - j) * f j) +
        ∑ j ∈ Finset.range (i + 1), β ^ (i - j) * f (J + j) := by
  rw [show J + i + 1 = J + (i + 1) by omega, Finset.sum_range_add]
  have hfirst : (∑ j ∈ Finset.range J, β ^ (J + i - j) * f j) =
      β ^ i * ∑ j ∈ Finset.range J, β ^ (J - j) * f j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjJ : j ≤ J := (Finset.mem_range.mp hj).le
    rw [show J + i - j = i + (J - j) by omega, pow_add]
    ring
  have hlast : (∑ j ∈ Finset.range (i + 1), β ^ (J + i - (J + j)) * f (J + j)) =
      ∑ j ∈ Finset.range (i + 1), β ^ (i - j) * f (J + j) := by
    congr 1
    funext j
    rw [show J + i - (J + j) = i - j by omega]
  rw [hfirst, hlast, pow_add]
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem quadratic_le_opNorm (D : E →L[ℝ] E) (v : E) :
    ⟪v, D v⟫_ℝ ≤ ‖D‖ * ‖v‖ ^ 2 := by
  calc
    _ ≤ ‖v‖ * ‖D v‖ := real_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖D‖ * ‖v‖) := mul_le_mul_of_nonneg_left (D.le_opNorm v) (norm_nonneg _)
    _ = _ := by ring

/-- The initial contribution is bounded by a finite scalar, regardless
of whether small-mass control holds at the omitted scales. -/
theorem finite_envelope_prefix_bound (N : ℕ → E →L[ℝ] E)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (J : ℕ) (v : E) :
    β ^ J * ‖v‖ ^ 2 + ∑ j ∈ Finset.range J, β ^ (J - j) * ⟪v, N j v⟫_ℝ ≤
      (1 + ∑ j ∈ Finset.range J, β ^ (J - j) * ‖N j‖) * ‖v‖ ^ 2 := by
  have hfirst := mul_le_mul_of_nonneg_right (pow_le_one₀ (n := J) hβ hβ1) (sq_nonneg ‖v‖)
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range J) =>
    mul_le_mul_of_nonneg_left (quadratic_le_opNorm (N j) v) (pow_nonneg hβ (J - j)))
  simp only [← mul_assoc, ← Finset.sum_mul] at hsum
  nlinarith only [hfirst, hsum]

/-- An eventual heat envelope has a finite background constant and the
unchanged small-mass convolution after shifting the starting index. -/
theorem shifted_heat_envelope_bound (N F : ℕ → E →L[ℝ] E)
    {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (henv : ∀ i v, ⟪v, F i v⟫_ℝ ≤ β ^ i * ‖v‖ ^ 2 +
      ∑ j ∈ Finset.range (i + 1), β ^ (i - j) * ⟪v, N j v⟫_ℝ)
    (J i : ℕ) (v : E) :
    ⟪v, F (J + i) v⟫_ℝ ≤
      (1 + ∑ j ∈ Finset.range J, β ^ (J - j) * ‖N j‖) * β ^ i * ‖v‖ ^ 2 +
        ∑ j ∈ Finset.range (i + 1), β ^ (i - j) * ⟪v, N (J + j) v⟫_ℝ := by
  have h := henv (J + i) v
  rw [geometric_envelope_shift] at h
  have hp := mul_le_mul_of_nonneg_left (finite_envelope_prefix_bound N hβ hβ1 J v)
    (pow_nonneg hβ i)
  nlinarith only [h, hp]

end RegularPointCoordinates

end

end OAI
