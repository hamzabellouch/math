import OAI.Geometry.RCD.Heat.GaussianErrorBudget
import OAI.Geometry.RCD.Heat.DirectionalHeatError

namespace OAI

/-! # From local directional errors to actual cutoff heat errors -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
/-- A bounded integrable nonnegative weight makes the directional Gram
error integrable, even when the reference measure is infinite. -/
theorem weighted_direction_error_integrable (u : SobolevSpace μ hQ) (c : ℝ)
    {w : X → ℝ} (hw : AEStronglyMeasurable w μ) {C : ℝ≥0}
    (hb : ∀ᵐ x ∂μ, ‖w x‖ ≤ (C : ℝ)) (hi : Integrable w μ)
    (hpos : ∀ᵐ x ∂μ, 0 ≤ w x) :
    Integrable (fun x => w x * |localGamma μ hQ u u x - c|) μ := by
  have hf := ((localGamma_memL1 μ hQ u u).bdd_mul hw hb).sub (hi.mul_const c)
  apply hf.abs.congr
  filter_upwards [hpos] with x hx
  simp only [Pi.sub_apply, ← mul_sub, abs_mul, abs_of_nonneg hx]

variable [μ.Regular]
  {k : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ k)
  {χ : X → ℝ} (hχ : Continuous χ) (hsχ : HasCompactSupport χ)

include hk hχ hsχ in
/-- A ball error budget is integrated using the actual heat kernel. The
Gaussian bound is used only where the cutoff is nonzero. -/
theorem cutoff_heat_direction_error_le_series (u : SobolevSpace μ hQ) (c : ℝ)
    (n : ℕ) (p : X) {r C V D B : ℝ} (hr : 0 < r)
    (hC : 0 ≤ C) (hV : 0 < V) (hD : 0 < D)
    (hχrange : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (hupper : ∀ y, k (r ^ 2) p y ≤ (C / μ.real (ball y r)) *
      Real.exp (-(dist p y) ^ 2 / (D * r ^ 2) + B * r ^ 2))
    (hvol : ∀ y, χ y ≠ 0 → V * r ^ n ≤ μ.real (ball y r))
    {e : ℕ → ℝ}
    (he : ∀ j, (∫ y in ball p (2 ^ j * r),
      χ y * |localGamma μ hQ u u y - c| ∂μ) ≤ e j)
    (hsum : Summable (fun j => gaussianShellFactor D⁻¹ j * e j)) :
    (∫ y, (χ y * k (r ^ 2) p y) * |localGamma μ hQ u u y - c| ∂μ) ≤
      ((C / (V * r ^ n)) * Real.exp (B * r ^ 2)) *
        ∑' j, gaussianShellFactor D⁻¹ j * e j := by
  have ht : 0 < r ^ 2 := sq_pos_of_pos hr
  have hχb : ∀ᵐ y ∂μ, ‖χ y‖ ≤ ((1 : ℝ≥0) : ℝ) :=
    Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hχrange y).1]
      exact (hχrange y).2
  have hfi := weighted_direction_error_integrable μ hQ u c hχ.aestronglyMeasurable hχb
    (hχ.integrable_of_hasCompactSupport hsχ)
    (Filter.Eventually.of_forall fun y => (hχrange y).1)
  have hwi := weighted_direction_error_integrable μ hQ u c
    (hχ.mul (hk.continuous_right _ ht p)).aestronglyMeasurable
    (Filter.Eventually.of_forall (cutoffHeatWeight_le μ hQ hk hχ hsχ ht p))
    ((hχ.mul (hk.continuous_right _ ht p)).integrable_of_hasCompactSupport hsχ.mul_right)
    (Filter.Eventually.of_forall fun y => mul_nonneg (hχrange y).1 (hk.nonneg _ ht p y))
  let L := (C / (V * r ^ n)) * Real.exp (B * r ^ 2)
  have hL : 0 ≤ L := mul_nonneg (div_nonneg hC (mul_pos hV (pow_pos hr _)).le)
    (Real.exp_pos _).le
  have hi : Integrable (fun y => k (r ^ 2) p y *
      (χ y * |localGamma μ hQ u u y - c|)) μ := by
    convert hwi using 1
    ext y
    simp only [Pi.mul_apply]
    ring
  have hbound (j : ℕ) : ∀ᵐ y ∂μ.restrict (dyadicShell p r j),
      k (r ^ 2) p y * (χ y * |localGamma μ hQ u u y - c|) ≤
        (L * gaussianShellFactor D⁻¹ j) * (χ y * |localGamma μ hQ u u y - c|) := by
    filter_upwards [ae_restrict_mem (measurableSet_dyadicShell p r j)] with y hy
    by_cases hz : χ y = 0
    · simp only [hz, zero_mul, mul_zero, le_refl]
    · exact mul_le_mul_of_nonneg_right
        (gaussian_shell_upper μ k n hr hC hV hD p j hy (hupper y) (hvol y hz))
        (mul_nonneg (hχrange y).1 (abs_nonneg _))
  have hb := integral_le_dyadic_shell_sum_of_product μ p hr hi
    (fun _ => hfi.integrableOn)
    (Filter.Eventually.of_forall fun y => mul_nonneg (hχrange y).1 (abs_nonneg _))
    (fun j => mul_nonneg hL (gaussianShellFactor_nonneg _ j))
    hbound he (by simpa only [mul_assoc] using hsum.mul_left L)
  simpa only [L, mul_assoc, mul_left_comm, tsum_mul_left] using hb

end RegularPointCoordinates

end

end OAI
