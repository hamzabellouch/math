import OAI.Analysis.IrrationalRotation.Model.FejerApproximation
import OAI.Analysis.IrrationalRotation.Analysis.FejerKernel
import OAI.Analysis.IrrationalRotation.Rotation.CircleKernelConvolution

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Invariant233.Fejer

private def bundledKernel (H : ℕ) : C(UnitAddCircle, ℝ) :=
  ⟨kernel H, continuous_kernel H⟩

theorem approximation_bounds (H : ℕ) (hH : H ≠ 0)
    {f : Circle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (x : Circle) :
    0 ≤ approximation H f x ∧ approximation H f x ≤ 1 :=
  CircleKernelConvolution.convolution_bounds (bundledKernel H)
    (kernel_nonneg H) (integral_kernel_volume H hH) hf hf0 hf1 x

theorem integral_approximation (H : ℕ) (hH : H ≠ 0)
    {f : Circle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    (∫ x, approximation H f x) = ∫ x, f x :=
  CircleKernelConvolution.integral_convolution (bundledKernel H)
    (integral_kernel_volume H hH) hf hf0 hf1

theorem approximation_eq_polynomial (H : ℕ)
    {f : Circle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (x : Circle) :
    (approximation H f x : ℂ) = FourierSampling.polynomial (frequencies H)
      (approximationCoefficient H f) x :=
  CircleKernelConvolution.convolution_eq_polynomial (bundledKernel H)
    (frequencies H) (coefficient H) (kernel_eq_finite_fourier_sum H) hf hf0 hf1 x

theorem approximationCoefficient_norm_le_one (H : ℕ) (hH : H ≠ 0)
    {f : Circle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (v : ℤ) :
    ‖approximationCoefficient H f v‖ ≤ 1 := by
  rw [approximationCoefficient, norm_mul]
  have h₁ := coefficient_norm_le_one H hH v
  have h₂ := CircleKernelConvolution.norm_testCoefficient_le_one hf hf0 hf1 v
  change ‖coefficient H v‖ * ‖CircleKernelConvolution.testCoefficient f v‖ ≤ 1
  nlinarith [norm_nonneg (coefficient H v), norm_nonneg (CircleKernelConvolution.testCoefficient f v)]

@[simp] theorem approximationCoefficient_zero (H : ℕ) (hH : H ≠ 0) (f : Circle → ℝ) :
    approximationCoefficient H f 0 = (∫ x, f x : ℝ) := by
  simp [approximationCoefficient, coefficient_zero H hH, integral_complex_ofReal]

theorem continuous_approximation (H : ℕ)
    {f : Circle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    Continuous (approximation H f) := by
  have hpoly : Continuous (fun x : Circle =>
      FourierSampling.polynomial (frequencies H) (approximationCoefficient H f) x) := by
    unfold FourierSampling.polynomial
    exact continuous_finsetSum _ (fun v hv => continuous_const.mul (fourier v).continuous)
  have heq : approximation H f = fun x =>
      (FourierSampling.polynomial (frequencies H) (approximationCoefficient H f) x).re := by
    funext x
    rw [← approximation_eq_polynomial H hf hf0 hf1 x]
    rfl
  rw [heq]
  exact Complex.continuous_re.comp hpoly

theorem approximation_l1_error_le (H : ℕ) (hH : H ≠ 0)
    {f : Circle → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    {B : Set Circle} (hB : MeasurableSet B) {δ ε : ℝ} (hδ : 0 ≤ δ)
    (hsmall : ∀ t ∈ B, CircleKernelConvolution.translationError f t ≤ δ)
    (htail : (∫ t in Bᶜ, kernel H t) ≤ ε) :
    (∫ x, |approximation H f x - f x|) ≤ δ + ε :=
  CircleKernelConvolution.l1_error_le_small_translation_and_tail (bundledKernel H)
    (kernel_nonneg H) (integral_kernel_volume H hH) hf hf0 hf1 hB hδ hsmall htail

end Invariant233.Fejer

end

end OAI
