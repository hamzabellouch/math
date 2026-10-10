import OAI.Geometry.RCD.Sobolev.ScalarAbsorption
import Mathlib.Analysis.Normed.Operator.Basic

namespace OAI

/-!
# Quantitative bounds for the differential update

The vectors `v`, `v1`, and `v2` stand for a field and its first and second
directional derivatives. The operators `K`, `K1`, and `K2` stand for the
inverse transpose and its directional derivatives. Their stated bounds
are used directly, with an arbitrary real-valued dual-size function.
The algebra does not assume the desired increment or recurrence estimates.
-/

namespace RegularPointCoordinates

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The first derivative increment has the square-root forcing bound. -/
theorem differential_first_increment_norm_le
    (K K1 : E →L[ℝ] F) (dual : E → ℝ) (v v1 : E)
    {C epsilon q r z energy : ℝ} (hC : 1 ≤ C) (hq : 0 < q) (hr : 0 < r)
    (hK : ∀ w, ‖K w‖ ≤ C * dual w)
    (hK1 : ∀ w, ‖K1 w‖ ≤ C * q / r * dual w)
    (hv : dual v ≤ C * Real.sqrt epsilon * r * Real.sqrt energy)
    (hv1 : dual v1 ≤ C * Real.sqrt epsilon *
      (Real.sqrt z + Real.sqrt energy * q)) :
    ‖K v1 + K1 v‖ ≤ C ^ 2 * Real.sqrt epsilon *
      (Real.sqrt z + 2 * Real.sqrt energy * q) := by
  have hC0 : 0 ≤ C := by linarith
  have h1 := (hK v1).trans (mul_le_mul_of_nonneg_left hv1 hC0)
  have h0 := (hK1 v).trans
    (mul_le_mul_of_nonneg_left hv (show 0 ≤ C * q / r by positivity))
  have hcancel : C * q / r * (C * Real.sqrt epsilon * r * Real.sqrt energy) =
      C ^ 2 * Real.sqrt epsilon * Real.sqrt energy * q := by
    field_simp [ne_of_gt hr]
  rw [hcancel] at h0
  calc
    _ ≤ ‖K v1‖ + ‖K1 v‖ := norm_add_le _ _
    _ ≤ C * (C * Real.sqrt epsilon * (Real.sqrt z + Real.sqrt energy * q)) +
        C ^ 2 * Real.sqrt epsilon * Real.sqrt energy * q := add_le_add h1 h0
    _ = _ := by ring

/-- The squared first increment in `re:squared-increment`. -/
theorem differential_first_increment_sq_le
    (K K1 : E →L[ℝ] F) (dual : E → ℝ) (v v1 : E)
    {C epsilon q r z energy : ℝ} (hC : 1 ≤ C)
    (hepsilon : 0 ≤ epsilon) (hq : 0 < q) (hr : 0 < r)
    (hz : 0 ≤ z) (henergy : 0 ≤ energy)
    (hK : ∀ w, ‖K w‖ ≤ C * dual w)
    (hK1 : ∀ w, ‖K1 w‖ ≤ C * q / r * dual w)
    (hv : dual v ≤ C * Real.sqrt epsilon * r * Real.sqrt energy)
    (hv1 : dual v1 ≤ C * Real.sqrt epsilon *
      (Real.sqrt z + Real.sqrt energy * q)) :
    ‖K v1 + K1 v‖ ^ 2 ≤ 5 * C ^ 4 * epsilon * (z + energy * q ^ 2) := by
  have hnorm := differential_first_increment_norm_le K K1 dual v v1
    hC hq hr hK hK1 hv hv1
  have henergySq : (Real.sqrt energy * q) ^ 2 = energy * q ^ 2 := by
    rw [mul_pow, Real.sq_sqrt henergy]
  have hforce : (Real.sqrt z + 2 * Real.sqrt energy * q) ^ 2 ≤
      5 * (z + energy * q ^ 2) := by
    nlinarith [Real.sq_sqrt hz, henergySq,
      sq_nonneg (2 * Real.sqrt z - Real.sqrt energy * q)]
  calc
    _ ≤ (C ^ 2 * Real.sqrt epsilon *
        (Real.sqrt z + 2 * Real.sqrt energy * q)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = C ^ 4 * epsilon * (Real.sqrt z + 2 * Real.sqrt energy * q) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hepsilon]
      ring
    _ ≤ C ^ 4 * epsilon * (5 * (z + energy * q ^ 2)) :=
      mul_le_mul_of_nonneg_left hforce (by positivity)
    _ = _ := by ring

/-- Before rescaling, the three second-derivative terms are controlled
by the same forcing. -/
theorem differential_second_increment_norm_le
    (K K1 K2 : E →L[ℝ] F) (dual : E → ℝ) (v v1 v2 : E)
    {C epsilon q r z energy : ℝ} (hC : 1 ≤ C)
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hq : 0 < q) (hr : 0 < r)
    (hK : ∀ w, ‖K w‖ ≤ C * dual w)
    (hK1 : ∀ w, ‖K1 w‖ ≤ C * q / r * dual w)
    (hK2 : ∀ w, ‖K2 w‖ ≤ C * q ^ 2 / r ^ 2 * dual w)
    (hv : dual v ≤ C * Real.sqrt epsilon * r * Real.sqrt energy)
    (hv1 : dual v1 ≤ C * Real.sqrt epsilon *
      (Real.sqrt z + Real.sqrt energy * q))
    (hv2 : dual v2 ≤ C / r * (Real.sqrt z * q + Real.sqrt energy * q ^ 2)) :
    ‖K v2 + (2 : ℝ) • K1 v1 + K2 v‖ ≤
      4 * (C ^ 2 * q / r) * (Real.sqrt z + Real.sqrt energy * q) := by
  have hC0 : 0 ≤ C := by linarith
  have hsqrt : Real.sqrt epsilon ≤ 1 := by
    nlinarith [Real.sq_sqrt hepsilon, Real.sqrt_nonneg epsilon]
  have hscale : 0 ≤ C ^ 2 * q / r := by positivity
  have hforce : 0 ≤ Real.sqrt z + Real.sqrt energy * q := by positivity
  have h0 : ‖K v2‖ ≤ (C ^ 2 * q / r) * (Real.sqrt z + Real.sqrt energy * q) := by
    calc
      _ ≤ C * (C / r * (Real.sqrt z * q + Real.sqrt energy * q ^ 2)) :=
        (hK v2).trans (mul_le_mul_of_nonneg_left hv2 hC0)
      _ = _ := by ring
  have h1 : ‖K1 v1‖ ≤ (C ^ 2 * q / r) * (Real.sqrt z + Real.sqrt energy * q) := by
    calc
      _ ≤ C * q / r * (C * Real.sqrt epsilon *
          (Real.sqrt z + Real.sqrt energy * q)) :=
        (hK1 v1).trans (mul_le_mul_of_nonneg_left hv1 (by positivity))
      _ = (C ^ 2 * q / r) *
          (Real.sqrt epsilon * (Real.sqrt z + Real.sqrt energy * q)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hforce hsqrt) hscale
  have h2 : ‖K2 v‖ ≤ (C ^ 2 * q / r) * (Real.sqrt z + Real.sqrt energy * q) := by
    calc
      _ ≤ C * q ^ 2 / r ^ 2 * (C * Real.sqrt epsilon * r * Real.sqrt energy) :=
        (hK2 v).trans (mul_le_mul_of_nonneg_left hv (by positivity))
      _ = (C ^ 2 * q / r) * (Real.sqrt epsilon * (Real.sqrt energy * q)) := by
        field_simp [ne_of_gt hr]
      _ ≤ (C ^ 2 * q / r) * (Real.sqrt energy * q) :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (by positivity) hsqrt) hscale
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.sqrt_nonneg _)) hscale
  calc
    _ ≤ ‖K v2 + (2 : ℝ) • K1 v1‖ + ‖K2 v‖ := norm_add_le _ _
    _ ≤ (‖K v2‖ + ‖(2 : ℝ) • K1 v1‖) + ‖K2 v‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ = ‖K v2‖ + 2 * ‖K1 v1‖ + ‖K2 v‖ := by norm_num [norm_smul]
    _ ≤ (C ^ 2 * q / r) * (Real.sqrt z + Real.sqrt energy * q) +
        2 * ((C ^ 2 * q / r) * (Real.sqrt z + Real.sqrt energy * q)) +
        (C ^ 2 * q / r) * (Real.sqrt z + Real.sqrt energy * q) :=
      add_le_add (add_le_add h0 (mul_le_mul_of_nonneg_left h1 (by norm_num))) h2
    _ = _ := by ring

/-- The dyadic normalization of the actual second increment. -/
theorem differential_second_increment_normalized_le
    (K K1 K2 : E →L[ℝ] F) (dual : E → ℝ) (v v1 v2 : E)
    {C epsilon q r z energy : ℝ} (hC : 1 ≤ C)
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hq : 0 < q) (hr : 0 < r)
    (hK : ∀ w, ‖K w‖ ≤ C * dual w)
    (hK1 : ∀ w, ‖K1 w‖ ≤ C * q / r * dual w)
    (hK2 : ∀ w, ‖K2 w‖ ≤ C * q ^ 2 / r ^ 2 * dual w)
    (hv : dual v ≤ C * Real.sqrt epsilon * r * Real.sqrt energy)
    (hv1 : dual v1 ≤ C * Real.sqrt epsilon *
      (Real.sqrt z + Real.sqrt energy * q))
    (hv2 : dual v2 ≤ C / r * (Real.sqrt z * q + Real.sqrt energy * q ^ 2)) :
    r / (2 * q) * ‖K v2 + (2 : ℝ) • K1 v1 + K2 v‖ ≤
      2 * C ^ 2 * (Real.sqrt z + Real.sqrt energy * q) := by
  have h := mul_le_mul_of_nonneg_left
    (differential_second_increment_norm_le K K1 K2 dual v v1 v2
      hC hepsilon hepsilon1 hq hr hK hK1 hK2 hv hv1 hv2)
    (show 0 ≤ r / (2 * q) by positivity)
  convert h using 1
  field_simp [ne_of_gt hr, ne_of_gt hq]
  ring

omit [NormedSpace ℝ F] in
/-- Increasing the directional metric and halving the radius give the
contractive half of the diagonal recurrence. -/
theorem diagonal_recurrence_of_increment_bound (old increment next : F)
    {q qnext r forcing : ℝ} (hq : 0 < q) (hr : 0 < r) (hmetric : q ≤ qnext)
    (hnext : next = old + increment)
    (hincrement : r / (2 * q) * ‖increment‖ ≤ forcing) :
    (r / 2) / qnext * ‖next‖ ≤ (r / q * ‖old‖) / 2 + forcing := by
  rw [hnext]
  calc
    _ ≤ (r / 2) / q * ‖old + increment‖ :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by positivity) hq hmetric) (norm_nonneg _)
    _ ≤ (r / 2) / q * (‖old‖ + ‖increment‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ = (r / q * ‖old‖) / 2 + r / (2 * q) * ‖increment‖ := by ring
    _ ≤ _ := add_le_add le_rfl hincrement

/-- The complete diagonal recurrence for an update with the actual
three-term second derivative increment. -/
theorem differential_diagonal_update_recurrence
    (K K1 K2 : E →L[ℝ] F) (dual : E → ℝ) (v v1 v2 : E) (old next : F)
    {C epsilon q qnext r z energy : ℝ} (hC : 1 ≤ C)
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hq : 0 < q) (hr : 0 < r) (hmetric : q ≤ qnext)
    (hK : ∀ w, ‖K w‖ ≤ C * dual w)
    (hK1 : ∀ w, ‖K1 w‖ ≤ C * q / r * dual w)
    (hK2 : ∀ w, ‖K2 w‖ ≤ C * q ^ 2 / r ^ 2 * dual w)
    (hv : dual v ≤ C * Real.sqrt epsilon * r * Real.sqrt energy)
    (hv1 : dual v1 ≤ C * Real.sqrt epsilon *
      (Real.sqrt z + Real.sqrt energy * q))
    (hv2 : dual v2 ≤ C / r * (Real.sqrt z * q + Real.sqrt energy * q ^ 2))
    (hnext : next = old + (K v2 + (2 : ℝ) • K1 v1 + K2 v)) :
    (r / 2) / qnext * ‖next‖ ≤ (r / q * ‖old‖) / 2 +
      2 * C ^ 2 * (Real.sqrt z + Real.sqrt energy * q) := by
  exact diagonal_recurrence_of_increment_bound old _ next hq hr hmetric hnext
    (differential_second_increment_normalized_le K K1 K2 dual v v1 v2
      hC hepsilon hepsilon1 hq hr hK hK1 hK2 hv hv1 hv2)

end RegularPointCoordinates

end OAI
