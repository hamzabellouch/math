import OAI.Geometry.RCD.Coordinates.AffineFitRecurrence

namespace OAI

/-! # Smoothing the actual past-source affine recurrence

The radial correction at scale i uses the defect P i, whereas its improved
fit is at scale i+m. The strict contraction margin absorbs this lag.
-/

namespace RegularPointCoordinates

theorem affine_fit_past_source_envelope {σ η A D lam : ℝ}
    (hσ : 0 ≤ σ) (hη : 0 ≤ η) (hA : 0 ≤ A) (hD : 0 ≤ D) (hlam : 0 ≤ lam)
    {P F : ℕ → ℝ} (hP : ∀ i, 0 ≤ P i) {m : ℕ} (hm : 0 < m)
    (hmargin : lam * A + D ≤ σ ^ m * A)
    (hinitial : ∀ i < m, F i ≤ A * (η * σ ^ i))
    (hstep : ∀ i, F (i + m) ≤ lam * F i + D * P i) :
    ∀ i, F i ≤ A * forwardDefect σ η P i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases hi : i < m
    · exact (hinitial i hi).trans (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (Finset.sum_nonneg fun j _ =>
          mul_nonneg (pow_nonneg hσ _) (hP j))) hA)
    · let j := i - m
      have hj : j < i := by dsimp only [j]; omega
      have hij : j + m = i := by dsimp only [j]; omega
      have henv : 0 ≤ forwardDefect σ η P j := forwardDefect_nonneg hσ hη hP j
      have hsrc := le_forwardDefect hσ hη hP j
      have hprop := forwardDefect_propagates (η := η) hσ hP j m
      calc
        F i = F (j + m) := by rw [hij]
        _ ≤ lam * F j + D * P j := hstep j
        _ ≤ lam * (A * forwardDefect σ η P j) + D * forwardDefect σ η P j :=
          add_le_add (mul_le_mul_of_nonneg_left (ih j hj) hlam)
            (mul_le_mul_of_nonneg_left hsrc hD)
        _ = (lam * A + D) * forwardDefect σ η P j := by ring
        _ ≤ (σ ^ m * A) * forwardDefect σ η P j :=
          mul_le_mul_of_nonneg_right hmargin henv
        _ = A * (σ ^ m * forwardDefect σ η P j) := by ring
        _ ≤ A * forwardDefect σ η P (j + m) := mul_le_mul_of_nonneg_left hprop hA
        _ = _ := by rw [hij]

/-- Apply the lagged estimate to the square of a normalized scalar fit.
The only source is the original nonnegative Poisson-defect sequence. -/
theorem squared_fit_le_forwardDefect {σ η A a C : ℝ}
    (hσ : 0 ≤ σ) (hη : 0 ≤ η) (hA : 0 ≤ A) (ha : 0 ≤ a) (hC : 0 ≤ C)
    {P e : ℕ → ℝ} (hP : ∀ i, 0 ≤ P i) (he : ∀ i, 0 ≤ e i)
    {m : ℕ} (hm : 0 < m)
    (hmargin : (2 * a ^ 2) * A + 2 * C ^ 2 ≤ σ ^ m * A)
    (hinitial : ∀ i < m, (e i) ^ 2 ≤ A * (η * σ ^ i))
    (hstep : ∀ i, e (i + m) ≤ a * e i + C * Real.sqrt (P i)) :
    ∀ i, (e i) ^ 2 ≤ A * forwardDefect σ η P i := by
  apply affine_fit_past_source_envelope hσ hη hA (by positivity) (by positivity)
    hP hm hmargin hinitial
  intro i
  exact affine_fit_squared_step (he i) (he (i + m)) ha hC (hP i) (hstep i)

end RegularPointCoordinates

end OAI
