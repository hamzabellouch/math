import OAI.Geometry.RCD.Heat.HeatKernelDifferenceInput

namespace OAI

/-! # The actual averaged long-time kernel difference -/

open Set Metric MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

omit [MetricSpace X] in
/-- Averaging preserves a uniform bound on the pointwise kernel difference. -/
theorem kernelAverage_difference_le (μ : Measure X) (ker : ℝ → X → X → ℝ)
    {s : Set X} (hfinite : μ s ≠ ∞) (hvol : 0 < μ.real s)
    (t : ℝ) (x z : X) (hf : IntegrableOn (fun y => ker t y z) s μ)
    {B : ℝ} (hbound : ∀ᵐ y ∂μ.restrict s, |ker t y z - ker t x z| ≤ B) :
    |kernelAverage μ ker t s z - ker t x z| ≤ B := by
  have hc : IntegrableOn (fun _ : X => ker t x z) s μ := integrableOn_const hfinite
  have hd := hf.sub hc
  have hμ : (μ.restrict s).real univ = μ.real s := by
    simp only [Measure.real, Measure.restrict_apply_univ]
  have he : kernelAverage μ ker t s z - ker t x z =
      (μ.real s)⁻¹ * ∫ y in s, (ker t y z - ker t x z) ∂μ := by
    rw [integral_sub hf hc, integral_const, smul_eq_mul, hμ]
    dsimp only [kernelAverage]
    field_simp [ne_of_gt hvol]
  rw [he, abs_mul, abs_of_nonneg (inv_nonneg.mpr hvol.le)]
  calc
    _ ≤ (μ.real s)⁻¹ * ∫ y in s, |ker t y z - ker t x z| ∂μ :=
      mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs) (inv_nonneg.mpr hvol.le)
    _ ≤ (μ.real s)⁻¹ * ∫ _y in s, B ∂μ :=
      mul_le_mul_of_nonneg_left
        (integral_mono_ae hd.abs (integrableOn_const hfinite) hbound) (inv_nonneg.mpr hvol.le)
    _ = B := by rw [integral_const, smul_eq_mul, hμ]; field_simp

variable [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ) [μ.Regular]
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

include hk in
/-- The published kernel gradient estimate yields the long-time averaged
kernel bound with the exact displacement-to-heat-length factor. -/
theorem averaged_kernel_difference_bound
    {C D B : ℝ} (hC : 0 ≤ C)
    (hdifference : ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x y z : X, dist x y ≤ Real.sqrt t →
      |ker t x z - ker t y z| ≤
        (C / (Real.sqrt t * μ.real (ball z (Real.sqrt t)))) * dist x y *
          Real.exp (-(dist x z) ^ 2 / (D * t) + B * t))
    {t r A : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (_hr : 0 < r)
    (x q z : X) (hfinite : μ (ball q r) ≠ ∞) (hvol : 0 < μ.real (ball q r))
    (hcenter : dist x q ≤ A * r) (hscale : (A + 1) * r ≤ Real.sqrt t) :
    |kernelAverage μ ker t (ball q r) z - ker t x z| ≤
      (C / (Real.sqrt t * μ.real (ball z (Real.sqrt t)))) * ((A + 1) * r) *
        Real.exp (-(dist x z) ^ 2 / (D * t) + B * t) := by
  have hi : IntegrableOn (fun y => ker t y z) (ball q r) μ := by
    apply (hk.integrable t ht z).integrableOn.congr
    exact Eventually.of_forall fun y => hk.symmetric t ht z y
  apply kernelAverage_difference_le μ ker hfinite hvol t x z hi
  filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
  have hxy : dist x y ≤ (A + 1) * r := by
    have hyq : dist q y < r := by simpa only [mem_ball, dist_comm] using hy
    linarith [dist_triangle x q y]
  have hh := hdifference t ht ht1 x y z (hxy.trans hscale)
  rw [abs_sub_comm] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hxy (div_nonneg hC (mul_nonneg (Real.sqrt_nonneg _) measureReal_nonneg)))
    (Real.exp_pos _).le)

end RegularPointCoordinates

end

end OAI
