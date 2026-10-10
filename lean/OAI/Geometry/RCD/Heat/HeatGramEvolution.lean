import OAI.Geometry.RCD.Heat.HeatMeasureEvolution

namespace OAI

/-!
# Evolution of actual cutoff heat Grams

A weak measure Laplacian of the cutoff energy density gives its pointwise
heat derivative and the integrated Gram increment. A nonnegative shifted
source then implies monotonicity.
-/

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {p : ℝ → X → X → ℝ} (hp : IsContinuousHeatKernel μ hQ p)
  {χ : X → ℝ} (hχ : Continuous χ) (hsχ : HasCompactSupport χ)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (U : E →L[ℝ] SobolevSpace μ hQ)

/-- An all-time extension used only to state ordinary derivatives at
positive times; it agrees with the actual Gram wherever it is used. -/
def cutoffHeatGramAt (t : ℝ) (x : X) (lambda : ℝ) : E →L[ℝ] E :=
  if ht : 0 < t then cutoffHeatGram μ hQ hp hχ hsχ U ht x lambda else 0

theorem cutoffHeatGramAt_of_pos {t : ℝ} (ht : 0 < t) (x : X) (lambda : ℝ) :
    cutoffHeatGramAt μ hQ hp hχ hsχ U t x lambda =
      cutoffHeatGram μ hQ hp hχ hsχ U ht x lambda := by
  simp only [cutoffHeatGramAt, dite_eq_left ht]

/-- Identification with the continuous kernel representative, rather than
an almost-everywhere choice of the heat flow. -/
theorem cutoffHeatGram_kernel_energy (v : E) (f : SobolevSpace μ hQ)
    (hf : SobolevSpace.toLp μ hQ f =ᵐ[μ]
      fun z => χ z * (SobolevSpace.minimalSlope μ hQ (U v) z) ^ 2)
    {t : ℝ} (ht : 0 < t) (x : X) (lambda : ℝ) :
    ⟪v, cutoffHeatGram μ hQ hp hχ hsχ U ht x lambda v⟫_ℝ =
      kernelHeat μ hQ hp t (SobolevSpace.toLp μ hQ f) x + lambda * t * ‖v‖ ^ 2 := by
  rw [cutoffHeatGram_energy, kernelHeat_eq_integral μ hQ hp ht]
  congr 1
  apply integral_congr_ae
  filter_upwards [hf] with z hz
  rw [hz]
  ring

/-- Full measure-source differentiation of the actual heat Gram. -/
theorem cutoffHeatGram_hasDerivAt (v : E) (f : SobolevSpace μ hQ)
    (hf : SobolevSpace.toLp μ hQ f =ᵐ[μ]
      fun z => χ z * (SobolevSpace.minimalSlope μ hQ (U v) z) ^ 2)
    (ν : SignedMeasure X) (hν : IsMeasureLaplacian μ hQ f ν)
    (c : X) {R : ℝ} (hR : 0 < R)
    (hfs : ∀ᵐ z ∂μ, R < dist c z → SobolevSpace.toLp μ hQ f z = 0)
    (hνs : ν.variation (Metric.closedBall c R)ᶜ = 0)
    {t : ℝ} (ht : 0 < t) (x : X) (lambda : ℝ) :
    HasDerivAt (fun s => ⟪v, cutoffHeatGramAt μ hQ hp hχ hsχ U s x lambda v⟫_ℝ)
      ((∫ᵛ z, p t x z ∂<•ν) + lambda * ‖v‖ ^ 2) t := by
  have hd := (hν.kernelHeat_hasDerivAt μ hQ hp c hR hfs hνs ht x).add
    (((hasDerivAt_id t).const_mul lambda).mul_const (‖v‖ ^ 2))
  simp only [mul_one] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with s hs
  rw [cutoffHeatGramAt_of_pos μ hQ hp hχ hsχ U hs,
    cutoffHeatGram_kernel_energy μ hQ hp hχ hsχ U v f hf hs]
  rfl

/-- Integrating the source gives the actual Gram increment between any
positive times. No density for the signed source is assumed. -/
theorem cutoffHeatGram_sub_eq_integral (v : E) (f : SobolevSpace μ hQ)
    (hf : SobolevSpace.toLp μ hQ f =ᵐ[μ]
      fun z => χ z * (SobolevSpace.minimalSlope μ hQ (U v) z) ^ 2)
    (ν : SignedMeasure X) (hν : IsMeasureLaplacian μ hQ f ν)
    (c : X) {R : ℝ} (hR : 0 < R)
    (hfs : ∀ᵐ z ∂μ, R < dist c z → SobolevSpace.toLp μ hQ f z = 0)
    (hνs : ν.variation (Metric.closedBall c R)ᶜ = 0)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (x : X) (lambda : ℝ) :
    ⟪v, cutoffHeatGram μ hQ hp hχ hsχ U (hs.trans_le hst) x lambda v⟫_ℝ -
      ⟪v, cutoffHeatGram μ hQ hp hχ hsχ U hs x lambda v⟫_ℝ =
      (∫ r in s..t, (∫ᵛ z, p r x z ∂<•ν)) + lambda * (t - s) * ‖v‖ ^ 2 := by
  rw [cutoffHeatGram_kernel_energy μ hQ hp hχ hsχ U v f hf,
    cutoffHeatGram_kernel_energy μ hQ hp hχ hsχ U v f hf]
  have he := hν.kernelHeat_sub_eq_integral μ hQ hp c hR hfs hνs hs hst x
  linarith

/-- Positivity of the shifted source gives monotonicity of the actual
quadratic heat Gram on positive times. -/
theorem cutoffHeatGram_monotone (v : E) (f : SobolevSpace μ hQ)
    (hf : SobolevSpace.toLp μ hQ f =ᵐ[μ]
      fun z => χ z * (SobolevSpace.minimalSlope μ hQ (U v) z) ^ 2)
    (ν : SignedMeasure X) (hν : IsMeasureLaplacian μ hQ f ν)
    (c : X) {R : ℝ} (hR : 0 < R)
    (hfs : ∀ᵐ z ∂μ, R < dist c z → SobolevSpace.toLp μ hQ f z = 0)
    (hνs : ν.variation (Metric.closedBall c R)ᶜ = 0)
    (x : X) (lambda : ℝ)
    (hpos : ∀ t, 0 < t → 0 ≤ (∫ᵛ z, p t x z ∂<•ν) + lambda * ‖v‖ ^ 2)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    ⟪v, cutoffHeatGram μ hQ hp hχ hsχ U hs x lambda v⟫_ℝ ≤
      ⟪v, cutoffHeatGram μ hQ hp hχ hsχ U (hs.trans_le hst) x lambda v⟫_ℝ := by
  let F := fun r => ⟪v, cutoffHeatGramAt μ hQ hp hχ hsχ U r x lambda v⟫_ℝ
  have hmono : MonotoneOn F (Ioi 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi (0 : ℝ))
    · intro r hr
      exact (cutoffHeatGram_hasDerivAt μ hQ hp hχ hsχ U v f hf ν hν c hR hfs hνs hr x lambda).continuousAt.continuousWithinAt
    · intro r hr
      have hr' : 0 < r := by simpa only [interior_Ioi, mem_Ioi] using hr
      exact (cutoffHeatGram_hasDerivAt μ hQ hp hχ hsχ U v f hf ν hν c hR hfs hνs hr' x lambda).hasDerivWithinAt
    · intro r hr
      exact hpos r (by simpa only [interior_Ioi, mem_Ioi] using hr)
  simpa only [F, cutoffHeatGramAt_of_pos μ hQ hp hχ hsχ U hs,
    cutoffHeatGramAt_of_pos μ hQ hp hχ hsχ U (hs.trans_le hst)] using hmono hs (hs.trans_le hst) hst

end RegularPointCoordinates

end

end OAI
