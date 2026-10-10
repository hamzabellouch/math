import OAI.Geometry.RCD.Coordinates.PositiveForms

namespace OAI

/-! # Bilinear estimates from domination of symmetric quadratic forms -/

open scoped InnerProductSpace

namespace RegularPointCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Domination of the absolute quadratic form gives Cauchy--Schwarz with
the dominating form in both directions. The dominated operator may be signed. -/
theorem symmetric_domination_cauchy_schwarz (D P : E →L[ℝ] E)
    (hD : D.IsSymmetric) (hdom : ∀ v, |⟪v, D v⟫_ℝ| ≤ ⟪v, P v⟫_ℝ)
    (v w : E) :
    ⟪v, D w⟫_ℝ ^ 2 ≤ ⟪v, P v⟫_ℝ * ⟪w, P w⟫_ℝ := by
  have hsym : ⟪w, D v⟫_ℝ = ⟪v, D w⟫_ℝ := by
    rw [real_inner_comm]
    exact hD v w
  have hpoly : ∀ t : ℝ,
      0 ≤ ⟪w, P w⟫_ℝ * (t * t) + (-2 * ⟪v, D w⟫_ℝ) * t + ⟪v, P v⟫_ℝ := by
    intro t
    have hp := (abs_le.mp (hdom (v + t • w))).2
    have hm := (abs_le.mp (hdom (v - t • w))).1
    simp only [map_add, map_sub, map_smul, inner_add_left, inner_sub_left,
      inner_add_right, inner_sub_right, inner_smul_left, inner_smul_right,
      conj_trivial, hsym] at hp hm
    nlinarith only [hp, hm]
  have hd := discrim_le_zero hpoly
  unfold discrim at hd
  nlinarith only [hd]

/-- A small upper bound for the dominating form in one direction gives
the asymmetric bound used by the heat/mean source comparison. -/
theorem symmetric_domination_mixed (D P Q : E →L[ℝ] E)
    (hD : D.IsSymmetric) (hP : P.IsPositive)
    (hdom : ∀ v, |⟪v, D v⟫_ℝ| ≤ ⟪v, P v⟫_ℝ)
    {ε : ℝ} (hsmall : ∀ v, ⟪v, P v⟫_ℝ ≤ ε * ⟪v, Q v⟫_ℝ) (v w : E) :
    ⟪v, D w⟫_ℝ ^ 2 ≤ ε * ⟪v, P v⟫_ℝ * ⟪w, Q w⟫_ℝ := by
  calc
    _ ≤ ⟪v, P v⟫_ℝ * ⟪w, P w⟫_ℝ := symmetric_domination_cauchy_schwarz D P hD hdom v w
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (hsmall w) (hP.inner_nonneg_right v)
      nlinarith only [h]

end RegularPointCoordinates

end OAI
