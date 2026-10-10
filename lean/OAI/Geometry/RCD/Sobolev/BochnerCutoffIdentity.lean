import OAI.Geometry.RCD.Sobolev.LocalBochnerInput

namespace OAI

/-! # The canonical Bochner cutoff identity from local measure calculus -/

open Set Metric MeasureTheory
open scoped InnerProductSpace BoundedContinuousFunction NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [ProperSpace X] in
/-- Integrating the actual full Bochner source retains its singular part. -/
theorem integral_harmonicBochnerSource (U : E →L[ℝ] SobolevSpace μ hQ)
    (M : PositiveBilinearMeasure X E) (κ : ℝ) (v : E) (χ : X →ᵇ ℝ) :
    (∫ᵛ x, χ x ∂<•(harmonicBochnerSource μ hQ U M κ v)) =
      2 * ⟪v, M.weightedOperator χ v⟫_ℝ -
        2 * κ * ∫ x, χ x * localGamma μ hQ (U v) (U v) x ∂μ := by
  rw [harmonicBochnerSource, VectorMeasure.integral_sub_vectorMeasure
    (PositiveBilinearMeasure.integrable_weight χ _)
    (PositiveBilinearMeasure.integrable_weight χ _),
    VectorMeasure.integral_smul_vectorMeasure, VectorMeasure.integral_smul_vectorMeasure,
    integral_signedDensity _ (localGamma_memL1 μ hQ (U v) (U v))]
  have hM : ⟪v, M.weightedOperator χ v⟫_ℝ = ∫ᵛ x, χ x ∂<•(M.bilinear v v) := by
    rw [real_inner_comm]
    exact M.weightedOperator_inner χ v v
  rw [← hM]
  rfl

omit [ProperSpace X] in
/-- The local Bochner equation and the weak Laplacian of the cutoff give
the precise mass identity used by `bochner_mass_le_of_local_error`. -/
theorem LocalHarmonicEnergy.test_cutoff
    {U : E →L[ℝ] SobolevSpace μ hQ} {M : PositiveBilinearMeasure X E}
    {κ : ℝ} {p : X} {r : ℝ} {L : ℝ≥0} {v : E}
    (G : LocalHarmonicEnergy μ hQ U M κ p r L v)
    (χ : X →ᵇ ℝ) (hχs : HasCompactSupport (χ : X → ℝ))
    (hχΩ : tsupport (χ : X → ℝ) ⊆ ball p (2 * r))
    (c : SobolevSpace μ hQ) (hc : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ)
    (q : Lp ℝ 2 μ) (hq : IsWeakLaplacian μ hQ c q)
    (hqs : ∀ᵐ x ∂μ, x ∉ ball p (2 * r) → q x = 0) :
    ⟪v, M.weightedOperator χ v⟫_ℝ =
      (1 / 2 : ℝ) * (∫ x, localGamma μ hQ (U v) (U v) x * q x ∂μ) +
        κ * ∫ x, χ x * localGamma μ hQ (U v) (U v) x ∂μ := by
  have he := G.measure_laplacian c χ χ.continuous hχs hχΩ hc
  rw [integral_harmonicBochnerSource] at he
  have hw := hq G.energy
  rw [energyForm_comm μ hQ c G.energy, L2.inner_def] at hw
  have hi : (∫ x, ⟪q x, SobolevSpace.toLp μ hQ G.energy x⟫_ℝ ∂μ) =
      ∫ x, localGamma μ hQ (U v) (U v) x * q x ∂μ := by
    apply integral_congr_ae
    filter_upwards [(ae_restrict_iff' measurableSet_ball).mp G.representative, hqs]
      with x hx hqx
    by_cases hin : x ∈ ball p (2 * r)
    · rw [hx hin]
      simp only [RCLike.inner_apply, conj_trivial]
    · simp only [hqx hin, inner_zero_left, mul_zero]
  rw [hi] at hw
  linarith

end RegularPointCoordinates

end

end OAI
