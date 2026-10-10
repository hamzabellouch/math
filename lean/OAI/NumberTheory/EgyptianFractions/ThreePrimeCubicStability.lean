import Mathlib

namespace OAI
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem337.ThreePrimeCubicStability

/-- Exact polynomial factorization gives a norm estimate without choosing
common upper bounds for the two arguments. -/
theorem norm_cube_sub_cube_le (z w : ℂ) :
    ‖z ^ 3 - w ^ 3‖ ≤ ‖z - w‖ * (‖z‖ ^ 2 + ‖z‖ * ‖w‖ + ‖w‖ ^ 2) := by
  have hfactor : z ^ 3 - w ^ 3 = (z - w) * (z ^ 2 + z * w + w ^ 2) := by ring
  rw [hfactor, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖z ^ 2 + z * w + w ^ 2‖ ≤ ‖z ^ 2 + z * w‖ + ‖w ^ 2‖ := norm_add_le _ _
    _ ≤ (‖z ^ 2‖ + ‖z * w‖) + ‖w ^ 2‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ = _ := by simp only [norm_pow, norm_mul]

/-- Asymmetric uniform error estimate for two cubic expressions. -/
theorem norm_cube_sub_cube_le_of_bounds (z w : ℂ) {E M N : ℝ}
    (hE : 0 ≤ E) (hM : 0 ≤ M) (_hN : 0 ≤ N)
    (hdiff : ‖z - w‖ ≤ E) (hz : ‖z‖ ≤ M) (hw : ‖w‖ ≤ N) :
    ‖z ^ 3 - w ^ 3‖ ≤ E * (M ^ 2 + M * N + N ^ 2) := by
  apply (norm_cube_sub_cube_le z w).trans
  apply mul_le_mul hdiff _ (by positivity) hE
  exact add_le_add
    (add_le_add (pow_le_pow_left₀ (norm_nonneg _) hz 2)
      (mul_le_mul hz hw (norm_nonneg _) hM))
    (pow_le_pow_left₀ (norm_nonneg _) hw 2)

/-- Cubic approximation error integrated over an arbitrary finite-measure set.
No measurability or integrability is silently assumed: the Bochner norm bound
is valid also when the displayed integral is defined by zero. -/
theorem norm_cubic_error_integral_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} (hs : μ s < ∞)
    (F G ψ : α → ℂ) {E M N : ℝ}
    (hE : 0 ≤ E) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hdiff : ∀ x ∈ s, ‖F x - G x‖ ≤ E)
    (hF : ∀ x ∈ s, ‖F x‖ ≤ M) (hG : ∀ x ∈ s, ‖G x‖ ≤ N)
    (hψ : ∀ x ∈ s, ‖ψ x‖ ≤ 1) :
    ‖∫ x in s, (F x ^ 3 - G x ^ 3) * ψ x ∂μ‖ ≤
      E * (M ^ 2 + M * N + N ^ 2) * (μ s).toReal := by
  apply norm_setIntegral_le_of_norm_le_const hs
  intro x hx
  rw [norm_mul]
  calc
    ‖F x ^ 3 - G x ^ 3‖ * ‖ψ x‖ ≤
        (E * (M ^ 2 + M * N + N ^ 2)) * 1 :=
      mul_le_mul (norm_cube_sub_cube_le_of_bounds (F x) (G x) hE hM hN
        (hdiff x hx) (hF x hx) (hG x hx)) (hψ x hx) (norm_nonneg _) (by positivity)
    _ = _ := mul_one _

/-- A common amplitude bound gives the standard `3 E M²` cubic error. -/
theorem norm_cubic_error_integral_le_common {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} (hs : μ s < ∞)
    (F G ψ : α → ℂ) {E M : ℝ} (hE : 0 ≤ E) (hM : 0 ≤ M)
    (hdiff : ∀ x ∈ s, ‖F x - G x‖ ≤ E)
    (hF : ∀ x ∈ s, ‖F x‖ ≤ M) (hG : ∀ x ∈ s, ‖G x‖ ≤ M)
    (hψ : ∀ x ∈ s, ‖ψ x‖ ≤ 1) :
    ‖∫ x in s, (F x ^ 3 - G x ^ 3) * ψ x ∂μ‖ ≤
      3 * E * M ^ 2 * (μ s).toReal := by
  convert norm_cubic_error_integral_le hs F G ψ hE hM hM hdiff hF hG hψ using 1
  ring

/-- When the two cubic integrands are integrable, the error estimate controls
the difference of their integrals, as required by major-arc approximation. -/
theorem norm_cubic_integral_sub_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {s : Set α} (hs : μ s < ∞)
    (F G ψ : α → ℂ) {E M : ℝ} (hE : 0 ≤ E) (hM : 0 ≤ M)
    (hFi : IntegrableOn (fun x => F x ^ 3 * ψ x) s μ)
    (hGi : IntegrableOn (fun x => G x ^ 3 * ψ x) s μ)
    (hdiff : ∀ x ∈ s, ‖F x - G x‖ ≤ E)
    (hF : ∀ x ∈ s, ‖F x‖ ≤ M) (hG : ∀ x ∈ s, ‖G x‖ ≤ M)
    (hψ : ∀ x ∈ s, ‖ψ x‖ ≤ 1) :
    ‖(∫ x in s, F x ^ 3 * ψ x ∂μ) - (∫ x in s, G x ^ 3 * ψ x ∂μ)‖ ≤
      3 * E * M ^ 2 * (μ s).toReal := by
  rw [← integral_sub hFi hGi]
  simpa only [sub_mul] using
    norm_cubic_error_integral_le_common hs F G ψ hE hM hdiff hF hG hψ

/-- Oriented-interval version of cubic stability, independent of endpoint order. -/
theorem norm_cubic_interval_error_le (F G ψ : ℝ → ℂ) (a b : ℝ)
    {E M : ℝ} (hE : 0 ≤ E) (hM : 0 ≤ M)
    (hdiff : ∀ x ∈ Set.uIoc a b, ‖F x - G x‖ ≤ E)
    (hF : ∀ x ∈ Set.uIoc a b, ‖F x‖ ≤ M)
    (hG : ∀ x ∈ Set.uIoc a b, ‖G x‖ ≤ M)
    (hψ : ∀ x ∈ Set.uIoc a b, ‖ψ x‖ ≤ 1) :
    ‖∫ x in a..b, (F x ^ 3 - G x ^ 3) * ψ x‖ ≤
      3 * E * M ^ 2 * |b - a| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  have hbound : ‖F x ^ 3 - G x ^ 3‖ ≤ 3 * E * M ^ 2 := by
    convert norm_cube_sub_cube_le_of_bounds (F x) (G x) hE hM hM
      (hdiff x hx) (hF x hx) (hG x hx) using 1
    ring
  rw [norm_mul]
  calc
    _ ≤ (3 * E * M ^ 2) * 1 :=
      mul_le_mul hbound (hψ x hx) (norm_nonneg _) (by positivity)
    _ = _ := mul_one _

end Problem337.ThreePrimeCubicStability

end

end OAI
