import OAI.Geometry.RCD.Coordinates.AffineFitSmoothing

namespace OAI

/-! # Smoothing radial fits with changing covector norms -/

namespace RegularPointCoordinates

/-- Dividing by the current covector norm introduces only the proved
growth loss across the fixed lag. No uniform Euclidean norm is required. -/
theorem weighted_fit_normalized_step {e w P : ℕ → ℝ} {a C G : ℝ} {m : ℕ}
    (ha : 0 ≤ a) (hC : 0 ≤ C)
    (he : ∀ i, 0 ≤ e i) (hw : ∀ i, 0 < w i)
    (hgrowth : ∀ i, w i ≤ G * w (i + m))
    (hstep : ∀ i, e (i + m) ≤ a * e i + C * w i * Real.sqrt (P i)) (i : ℕ) :
    e (i + m) / w (i + m) ≤ (a * G) * (e i / w i) + (C * G) * Real.sqrt (P i) := by
  have hr : 0 ≤ w i / w (i + m) := div_nonneg (hw i).le (hw _).le
  have hrG : w i / w (i + m) ≤ G := (div_le_iff₀ (hw _)).mpr (hgrowth i)
  have hei : 0 ≤ e i / w i := div_nonneg (he i) (hw i).le
  have h₁ := mul_le_mul_of_nonneg_left hrG (mul_nonneg ha hei)
  have h₂ := mul_le_mul_of_nonneg_left hrG (mul_nonneg hC (Real.sqrt_nonneg (P i)))
  calc
    _ ≤ (a * e i + C * w i * Real.sqrt (P i)) / w (i + m) :=
      div_le_div_of_nonneg_right (hstep i) (hw _).le
    _ = (a * (e i / w i)) * (w i / w (i + m)) +
        (C * Real.sqrt (P i)) * (w i / w (i + m)) := by
      field_simp [(hw i).ne', (hw (i + m)).ne']
    _ ≤ (a * (e i / w i)) * G + (C * Real.sqrt (P i)) * G := add_le_add h₁ h₂
    _ = _ := by ring

/-- The smoothed error controls each original fit in its own covector
norm. The defect sequence is unchanged by normalization. -/
theorem weighted_squared_fit_le_forwardDefect {σ η A a C G : ℝ}
    (hσ : 0 ≤ σ) (hη : 0 ≤ η) (hA : 0 ≤ A)
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hG : 0 ≤ G)
    {P e w : ℕ → ℝ} (hP : ∀ i, 0 ≤ P i) (he : ∀ i, 0 ≤ e i) (hw : ∀ i, 0 < w i)
    {m : ℕ} (hm : 0 < m)
    (hmargin : (2 * (a * G) ^ 2) * A + 2 * (C * G) ^ 2 ≤ σ ^ m * A)
    (hinitial : ∀ i < m, (e i / w i) ^ 2 ≤ A * (η * σ ^ i))
    (hgrowth : ∀ i, w i ≤ G * w (i + m))
    (hstep : ∀ i, e (i + m) ≤ a * e i + C * w i * Real.sqrt (P i)) :
    ∀ i, (e i) ^ 2 ≤ A * forwardDefect σ η P i * (w i) ^ 2 := by
  have hb := squared_fit_le_forwardDefect hσ hη hA (mul_nonneg ha hG) (mul_nonneg hC hG)
    hP (fun i => div_nonneg (he i) (hw i).le) hm hmargin hinitial
    (weighted_fit_normalized_step ha hC he hw hgrowth hstep)
  intro i
  have hh := mul_le_mul_of_nonneg_right (hb i) (sq_nonneg (w i))
  rwa [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 (hw i).ne')] at hh

end RegularPointCoordinates

end OAI
