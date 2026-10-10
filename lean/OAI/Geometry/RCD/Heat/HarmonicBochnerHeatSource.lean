import OAI.Geometry.RCD.Heat.HarmonicBochnerHeat
import OAI.Geometry.RCD.Heat.ActualHeatMass

namespace OAI

/-!
# The canonical heat source as mass, curvature and cutoff error

A second compact cutoff legitimizes testing the full signed source against
an arbitrary positive-time continuous kernel row. The resulting formula
is the actual harmonic heat Gram equation, including singular Bochner mass.
-/

open Set Metric MeasureTheory
open scoped NNReal InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {U : E →L[ℝ] SobolevSpace μ hQ} {M : PositiveBilinearMeasure X E}
  {κ : ℝ} {p : X} {r : ℝ} {L : ℝ≥0} {v : E}

namespace LocalHarmonicEnergy

omit [ProperSpace X] in
/-- The explicit bounded-test decomposition of the full cutoff source. -/
theorem integral_cutoffSource (G : LocalHarmonicEnergy μ hQ U M κ p r L v)
    (χ w : X →ᵇ ℝ) (c : SobolevSpace μ hQ) (q : Lp ℝ 2 μ) :
    (∫ᵛ z, w z ∂<•(G.cutoffSource μ hQ χ c q)) =
      2 * ⟪v, M.weightedOperator (w * χ) v⟫_ℝ -
      2 * κ * (∫ z, (w * χ) z * localGamma μ hQ (U v) (U v) z ∂μ) +
      ∫ z, w z * cutoffSourceDensity μ hQ G.energy c q z ∂μ := by
  rw [cutoffSource, cutoffMeasureSource, VectorMeasure.integral_add_vectorMeasure
    (PositiveBilinearMeasure.integrable_weight w _)
    (PositiveBilinearMeasure.integrable_weight w _),
    integral_signedSourceWeight, integral_harmonicBochnerSource,
    integral_signedDensity _ (cutoffSourceDensity_integrable μ hQ G.energy c q)]

variable [μ.Regular] {k : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ k)

/-- Full signed integration against a kernel row splits into the actual
heat mass, the curvature term and the integrable cutoff error. -/
theorem kernel_cutoffSource (G : LocalHarmonicEnergy μ hQ U M κ p r L v)
    (χ : X →ᵇ ℝ) (hχs : HasCompactSupport (χ : X → ℝ))
    (c : SobolevSpace μ hQ) (hc : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ)
    (q : Lp ℝ 2 μ) (a : X) {R : ℝ} (hR : 0 < R)
    (hχR : ∀ z ∉ closedBall a R, χ z = 0)
    (hqR : ∀ᵐ z ∂μ, z ∉ closedBall a R → q z = 0)
    {t : ℝ} (ht : 0 < t) (x : X) :
    (∫ᵛ z, k t x z ∂<•(G.cutoffSource μ hQ χ c q)) =
      2 * ⟪v, cutoffHeatMass μ hQ hk χ.continuous hχs M ht x v⟫_ℝ -
      2 * κ * ⟪v, cutoffHeatGram μ hQ hk χ.continuous hχs U ht x 0 v⟫_ℝ +
      ∫ z, k t x z * cutoffSourceDensity μ hQ G.energy c q z ∂μ := by
  let η := radialCutoff a R
  have hη := (radialCutoff_lipschitz a hR).continuous
  have hsη := radialCutoff_hasCompactSupport a hR
  let w := cutoffHeatWeight μ hQ hk hη hsη ht x
  have hw (z : X) : w z = η z * k t x z := rfl
  have hνs := cutoffMeasureSource_variation_compl μ hQ G.energy c q
    (harmonicBochnerSource μ hQ U M κ v) χ hc measurableSet_closedBall hχR hqR
  have haew : (fun z => k t x z) =ᵐ[(G.cutoffSource μ hQ χ c q).variation] w := by
    have hm : ∀ᵐ z ∂(G.cutoffSource μ hQ χ c q).variation, z ∈ closedBall a R :=
      ae_iff.mpr hνs
    filter_upwards [hm] with z hz
    rw [hw, show η z = 1 from radialCutoff_eq_one a hR
      (by simpa only [mem_closedBall, dist_comm] using hz), one_mul]
  have hweight : w * χ = cutoffHeatWeight μ hQ hk χ.continuous hχs ht x := by
    ext z
    change w z * χ z = χ z * k t x z
    by_cases hz : z ∈ closedBall a R
    · rw [hw, show η z = 1 from radialCutoff_eq_one a hR
        (by simpa only [mem_closedBall, dist_comm] using hz)]
      ring
    · rw [hχR z hz, mul_zero, zero_mul]
  have herror := cutoffSourceDensity_zero_off μ hQ G.energy c q χ hc hχR hqR
  have herr : (∫ z, w z * cutoffSourceDensity μ hQ G.energy c q z ∂μ) =
      ∫ z, k t x z * cutoffSourceDensity μ hQ G.energy c q z ∂μ := by
    apply integral_congr_ae
    filter_upwards [herror] with z hz
    by_cases hin : z ∈ closedBall a R
    · rw [hw, show η z = 1 from radialCutoff_eq_one a hR
        (by simpa only [mem_closedBall, dist_comm] using hin), one_mul]
    · rw [hz hin, mul_zero, mul_zero]
  rw [VectorMeasure.integral_congr_ae haew, G.integral_cutoffSource μ hQ χ w c q,
    hweight, herr]
  change 2 * ⟪v, cutoffHeatMass μ hQ hk χ.continuous hχs M ht x v⟫_ℝ - _ + _ = _
  have hgram : (∫ z, cutoffHeatWeight μ hQ hk χ.continuous hχs ht x z *
      localGamma μ hQ (U v) (U v) z ∂μ) =
      ⟪v, cutoffHeatGram μ hQ hk χ.continuous hχs U ht x 0 v⟫_ℝ := by
    rw [cutoffHeatGram_energy]
    simp only [zero_mul, add_zero]
    apply integral_congr_ae
    filter_upwards [localGamma_self μ hQ (U v)] with z hz
    rw [hz]
    rfl
  rw [hgram]

/-- The actual heat Gram equation, now with the canonical mass term. -/
theorem heatGram_hasDerivAt_mass (G : LocalHarmonicEnergy μ hQ U M κ p r L v)
    (χ : X →ᵇ ℝ) (hχs : HasCompactSupport (χ : X → ℝ))
    (hχΩ : tsupport (χ : X → ℝ) ⊆ ball p (2 * r))
    (c : SobolevSpace μ hQ) (hc : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ)
    (q : Lp ℝ 2 μ) (hq : IsWeakLaplacian μ hQ c q)
    (a : X) {R : ℝ} (hR : 0 < R)
    (hχR : ∀ z ∉ closedBall a R, χ z = 0)
    (hqR : ∀ᵐ z ∂μ, z ∉ closedBall a R → q z = 0)
    {t : ℝ} (ht : 0 < t) (x : X) (lambda : ℝ) :
    HasDerivAt (fun s => ⟪v, cutoffHeatGramAt μ hQ hk χ.continuous hχs U s x lambda v⟫_ℝ)
      (2 * ⟪v, cutoffHeatMass μ hQ hk χ.continuous hχs M ht x v⟫_ℝ -
       2 * κ * ⟪v, cutoffHeatGram μ hQ hk χ.continuous hχs U ht x 0 v⟫_ℝ +
       (∫ z, k t x z * cutoffSourceDensity μ hQ G.energy c q z ∂μ) +
       lambda * ‖v‖ ^ 2) t := by
  have hd := G.heatGram_hasDerivAt μ hQ hk χ hχs hχΩ c hc q hq a hR hχR hqR ht x lambda
  rwa [G.kernel_cutoffSource μ hQ hk χ hχs c hc q a hR hχR hqR ht x] at hd

end LocalHarmonicEnergy
end RegularPointCoordinates

end

end OAI
