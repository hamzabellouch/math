import OAI.Geometry.RCD.Harmonic.WeightedInwardConstants

namespace OAI

/-! # Inward summation for the squared radial fit estimate -/

open Filter
open scoped Topology

noncomputable section
namespace RegularPointCoordinates

/-- The actual two-fit center estimate and the squared radial fit bound
give a quantitative center bound in the current covector norm. -/
theorem weighted_centers_from_squared_fit {ρ M Λ Z : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hτρ : (9 / 16 : ℝ) < Real.sqrt ρ)
    (hM : 0 ≤ M) (hΛ : 0 ≤ Λ) (hZ : 0 ≤ Z)
    {P c r w e : ℕ → ℝ} (hP : ∀ i, 0 ≤ P i) (hPs : Summable P)
    (hr : ∀ i, 0 ≤ r i) (hw : ∀ i, 0 ≤ w i) (he : ∀ i, 0 ≤ e i)
    (hradius : ∀ i k, r (i + k) = (1 / 2 : ℝ) ^ k * r i)
    (hgrowth : ∀ i k, w (i + k) ≤ (9 / 8 : ℝ) ^ k * w i)
    (hc : Tendsto c atTop (𝓝 0))
    (hsquare : ∀ i, (e i) ^ 2 ≤ Z * P i * (w i) ^ 2)
    (hstep : ∀ i, |c i - c (i + 1)| ≤ M * Λ * r i * e i + M * r (i + 1) * e (i + 1))
    (i : ℕ) :
    |c i| ≤ (M * (Λ + 1) * Real.sqrt Z) * r i * w i *
      (1 - (9 / 16 : ℝ) / Real.sqrt ρ)⁻¹ * (1 + (Real.sqrt ρ)⁻¹) *
      Real.sqrt (symmetricDefect ρ P i) := by
  have hfit (j : ℕ) : e j ≤ Real.sqrt Z * w j * Real.sqrt (P j) := by
    apply (sq_le_sq₀ (he j) (mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg Z) (hw j)) (Real.sqrt_nonneg (P j)))).mp
    calc
      (e j) ^ 2 ≤ Z * P j * (w j) ^ 2 := hsquare j
      _ = (Real.sqrt Z * w j * Real.sqrt (P j)) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hZ, Real.sq_sqrt (hP j)]
        ring
  have hcoeff : 0 ≤ M * (Λ + 1) * Real.sqrt Z := by positivity
  apply weighted_affine_constants_le_envelope hρ hρ1 hτρ hcoeff hP hPs hr hw hradius hgrowth hc
  intro j
  have hrw : r (j + 1) * w (j + 1) ≤ r j * w j := by
    have hg := hgrowth j 1
    simp only [pow_one] at hg
    rw [hradius j 1, pow_one]
    have hh := mul_le_mul_of_nonneg_left hg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (hr j))
    nlinarith [mul_nonneg (hr j) (hw j)]
  calc
    _ ≤ M * Λ * r j * e j + M * r (j + 1) * e (j + 1) := hstep j
    _ ≤ M * Λ * r j * (Real.sqrt Z * w j * Real.sqrt (P j)) +
        M * r (j + 1) * (Real.sqrt Z * w (j + 1) * Real.sqrt (P (j + 1))) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hfit j) (mul_nonneg (mul_nonneg hM hΛ) (hr j)))
        (mul_le_mul_of_nonneg_left (hfit (j + 1)) (mul_nonneg hM (hr (j + 1))))
    _ = M * Real.sqrt Z * (Λ * (r j * w j) * Real.sqrt (P j) +
        (r (j + 1) * w (j + 1)) * Real.sqrt (P (j + 1))) := by ring
    _ ≤ M * Real.sqrt Z * (Λ * (r j * w j) * Real.sqrt (P j) +
        (r j * w j) * Real.sqrt (P (j + 1))) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add_right (mul_le_mul_of_nonneg_right hrw (Real.sqrt_nonneg _)) _)
        (by positivity)
    _ ≤ (M * (Λ + 1) * Real.sqrt Z) * r j * w j *
        (Real.sqrt (P j) + Real.sqrt (P (j + 1))) := by
      have h0 := mul_nonneg (mul_nonneg (hr j) (hw j)) (Real.sqrt_nonneg (P j))
      have h1 := mul_nonneg (mul_nonneg (mul_nonneg hΛ (hr j)) (hw j))
        (Real.sqrt_nonneg (P (j + 1)))
      have hh := mul_nonneg (mul_nonneg hM (Real.sqrt_nonneg Z)) (add_nonneg h0 h1)
      nlinarith

end RegularPointCoordinates

end

end OAI
