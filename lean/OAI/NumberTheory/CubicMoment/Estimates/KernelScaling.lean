import OAI.NumberTheory.CubicMoment.Estimates.KernelTail

namespace OAI

/-!
# Scaling a cutoff kernel

The normalization and weighted L¹ moment are preserved under `T k(Tx)`.
Thus a single Schwartz kernel gives a uniform family of interval
approximations at all positive truncation heights.
-/

noncomputable section
open MeasureTheory

namespace CubicFirstMoment

def scaledKernel (k : ℝ → ℂ) (T y : ℝ) : ℂ := (T : ℂ) * k (T*y)

theorem integrable_scaledKernel {k : ℝ → ℂ} (hk : Integrable k)
    {T : ℝ} (hT : 0 < T) : Integrable (scaledKernel k T) :=
  (hk.comp_mul_left' hT.ne').const_mul (T : ℂ)

theorem integral_scaledKernel (k : ℝ → ℂ) {T : ℝ} (hT : 0 < T) :
    (∫ y, scaledKernel k T y) = ∫ y, k y := by
  unfold scaledKernel
  rw [integral_const_mul, Measure.integral_comp_mul_left]
  simp only [abs_of_pos (inv_pos.mpr hT), Complex.real_smul, ← mul_assoc,
    ← Complex.ofReal_mul, mul_inv_cancel₀ hT.ne', Complex.ofReal_one, one_mul]

private theorem scaledKernel_moment_integrand (k : ℝ → ℂ) {T : ℝ} (hT : 0 < T) :
    (fun y => ‖scaledKernel k T y‖ * (1 + T*|y|)^2) =
      (fun y => T * (‖k (T*y)‖ * (1 + |T*y|)^2)) := by
  funext y
  simp only [scaledKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hT, abs_mul]
  ring

theorem integrable_scaledKernel_moment {k : ℝ → ℂ}
    (hM : Integrable (fun y => ‖k y‖ * (1 + |y|)^2))
    {T : ℝ} (hT : 0 < T) :
    Integrable (fun y => ‖scaledKernel k T y‖ * (1 + T*|y|)^2) := by
  rw [scaledKernel_moment_integrand k hT]
  exact (hM.comp_mul_left' hT.ne').const_mul T

theorem kernelMoment_scaledKernel (k : ℝ → ℂ) {T : ℝ} (hT : 0 < T) :
    kernelMoment (scaledKernel k T) T = kernelMoment k 1 := by
  rw [kernelMoment, scaledKernel_moment_integrand k hT, integral_const_mul,
    Measure.integral_comp_mul_left (fun y : ℝ => ‖k y‖ * (1 + |y|)^2) T]
  simp only [abs_of_pos (inv_pos.mpr hT), smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hT.ne', one_mul, kernelMoment]

/-- Schwartz decay supplies the integrable moment needed by the cutoff,
without imposing a quantitative tail estimate as a hypothesis. -/
theorem integrable_kernelMoment_schwartz (k : SchwartzMap ℝ ℂ) :
    Integrable (fun y => ‖k y‖ * (1 + |y|)^2) := by
  have h₀ : Integrable (fun y : ℝ => ‖k y‖) :=
    (show Integrable (fun y : ℝ => k y) from k.integrable).norm
  have h₁ := k.integrable_pow_mul volume 1
  have h₂ := k.integrable_pow_mul volume 2
  have h := h₀.add ((h₁.const_mul 2).add h₂)
  apply h.congr
  filter_upwards [] with y
  simp only [Pi.add_apply, Real.norm_eq_abs, pow_one]
  ring

/-- Uniform endpoint estimate for the entire scaled Schwartz family. -/
theorem scaled_schwartz_interval_error (k : SchwartzMap ℝ ℂ)
    (hmass : ∫ y, k y = 1) {T : ℝ} (hT : 0 < T) (a b s : ℝ) :
    ‖(intervalStep a b s : ℂ) - intervalSmoothing (scaledKernel k T) a b s‖ ≤
      kernelMoment k 1 / (1 + T*|s-a|)^2 +
        kernelMoment k 1 / (1 + T*|s-b|)^2 := by
  have h := intervalSmoothing_error_le_moment
    (integrable_scaledKernel k.integrable hT)
    ((integral_scaledKernel k hT).trans hmass) hT.le
    (integrable_scaledKernel_moment (integrable_kernelMoment_schwartz k) hT) a b s
  simpa only [kernelMoment_scaledKernel k hT] using h

end CubicFirstMoment

end

end OAI
