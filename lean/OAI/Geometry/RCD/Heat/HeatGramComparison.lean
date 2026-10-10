import OAI.Geometry.RCD.Heat.ActualHeatGrams

namespace OAI

/-! # Comparing actual heat Grams with local mean Grams -/

open Set MeasureTheory
open scoped InnerProductSpace NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ) [μ.Regular]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {p : ℝ → X → X → ℝ} (hp : IsContinuousHeatKernel μ hQ p)
  {χ : X → ℝ} (hχ : Continuous χ) (hsχ : HasCompactSupport χ)
  (U : E →L[ℝ] SobolevSpace μ hQ)

/-- A lower kernel bound on a set where the cutoff equals one gives a
lower bound by its actual mean Gram, including the positive regularizer. -/
theorem cutoffHeatGram_lower_mean (s : Set X) (hs : MeasurableSet s)
    (hχpos : ∀ y, 0 ≤ χ y) (hχone : ∀ y ∈ s, χ y = 1)
    {t : ℝ} (ht : 0 < t) (x : X) {c lambda : ℝ} (hlambda : 0 ≤ lambda)
    (hkernel : ∀ y ∈ s, c * (μ.real s)⁻¹ ≤ p t x y) (v : E) :
    c * ⟪v, sobolevMeanGram μ hQ U s hs v⟫_ℝ ≤
      ⟪v, cutoffHeatGram μ hQ hp hχ hsχ U ht x lambda v⟫_ℝ := by
  let g := fun y => (SobolevSpace.minimalSlope μ hQ (U v) y) ^ 2
  have hi : Integrable g μ :=
    (localGamma_memL1 μ hQ (U v) (U v)).congr (localGamma_self μ hQ (U v))
  have hweight : AEStronglyMeasurable (fun y => χ y * p t x y) μ :=
    (hχ.mul (hp.continuous_right t ht x)).aestronglyMeasurable
  have hib : Integrable (fun y => (χ y * p t x y) * g y) μ :=
    hi.bdd_mul hweight (Filter.Eventually.of_forall
      (cutoffHeatWeight_le μ hQ hp hχ hsχ ht x))
  have hlocal : c * (μ.real s)⁻¹ * (∫ y in s, g y ∂μ) ≤
      ∫ y in s, (χ y * p t x y) * g y ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hi.integrableOn.const_mul _) hib.integrableOn
    filter_upwards [ae_restrict_mem hs] with y hy
    rw [hχone y hy, one_mul]
    exact mul_le_mul_of_nonneg_right (hkernel y hy) (sq_nonneg _)
  have hglobal : (∫ y in s, (χ y * p t x y) * g y ∂μ) ≤
      ∫ y, (χ y * p t x y) * g y ∂μ :=
    setIntegral_le_integral hib (Filter.Eventually.of_forall fun y =>
      mul_nonneg (mul_nonneg (hχpos y) (hp.nonneg t ht x y)) (sq_nonneg _))
  rw [sobolevMeanGram_energy, cutoffHeatGram_energy]
  have hreg := mul_nonneg (mul_nonneg hlambda ht.le) (sq_nonneg ‖v‖)
  change c * ((μ.real s)⁻¹ * ∫ y in s, g y ∂μ) ≤
    (∫ y, (χ y * p t x y) * g y ∂μ) + _
  linarith

/-- An upper kernel bound on the support of a cutoff bounds the heat Gram
by the mean Gram on the supporting set and the exact regularizer. -/
theorem cutoffHeatGram_upper_mean (s : Set X) (hs : MeasurableSet s)
    (hχle : ∀ y, χ y ≤ 1) (hχzero : ∀ y ∉ s, χ y = 0)
    {t : ℝ} (ht : 0 < t) (x : X) {C lambda : ℝ}
    (hkernel : ∀ y ∈ s, p t x y ≤ C * (μ.real s)⁻¹) (v : E) :
    ⟪v, cutoffHeatGram μ hQ hp hχ hsχ U ht x lambda v⟫_ℝ ≤
      C * ⟪v, sobolevMeanGram μ hQ U s hs v⟫_ℝ + (lambda * t) * ‖v‖ ^ 2 := by
  let g := fun y => (SobolevSpace.minimalSlope μ hQ (U v) y) ^ 2
  have hi : Integrable g μ :=
    (localGamma_memL1 μ hQ (U v) (U v)).congr (localGamma_self μ hQ (U v))
  have hweight : AEStronglyMeasurable (fun y => χ y * p t x y) μ :=
    (hχ.mul (hp.continuous_right t ht x)).aestronglyMeasurable
  have hib : Integrable (fun y => (χ y * p t x y) * g y) μ :=
    hi.bdd_mul hweight (Filter.Eventually.of_forall
      (cutoffHeatWeight_le μ hQ hp hχ hsχ ht x))
  have hout : (∫ y, (χ y * p t x y) * g y ∂μ) =
      ∫ y in s, (χ y * p t x y) * g y ∂μ := by
    rw [← integral_indicator hs]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      by_cases hy : y ∈ s
      · simp only [Set.indicator_of_mem hy]
      · simp [hy, hχzero y hy]
  have hlocal : (∫ y in s, (χ y * p t x y) * g y ∂μ) ≤
      C * (μ.real s)⁻¹ * ∫ y in s, g y ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae hib.integrableOn (hi.integrableOn.const_mul _)
    filter_upwards [ae_restrict_mem hs] with y hy
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact (mul_le_of_le_one_left (hp.nonneg t ht x y) (hχle y)).trans (hkernel y hy)
  rw [cutoffHeatGram_energy, sobolevMeanGram_energy]
  change (∫ y, (χ y * p t x y) * g y ∂μ) + _ ≤
    C * ((μ.real s)⁻¹ * ∫ y in s, g y ∂μ) + _
  rw [hout]
  linarith

end RegularPointCoordinates

end

end OAI
