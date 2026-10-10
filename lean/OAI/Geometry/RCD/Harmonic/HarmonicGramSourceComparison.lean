import OAI.Geometry.RCD.Heat.SourceComparisonIdentity
import OAI.Geometry.RCD.Heat.HarmonicBochnerHeat

namespace OAI

/-! # Exact source formula for the actual mean and heat Gram forms -/

open Set Metric MeasureTheory Filter
open scoped InnerProductSpace NNReal BoundedContinuousFunction ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {U : E →L[ℝ] SobolevSpace μ hQ} {M : PositiveBilinearMeasure X E}
  {κ : ℝ} {p : X} {r : ℝ} {L : ℝ≥0} {v : E}

/-- Applying the genuine compact-source identity to the actual cutoff
energy gives the mean-minus-heat formula, including its scalar regularizer. -/
theorem LocalHarmonicEnergy.mean_sub_heat_source
    (G : LocalHarmonicEnergy μ hQ U M κ p r L v)
    (χ : X →ᵇ ℝ) (hχs : HasCompactSupport (χ : X → ℝ))
    (hχΩ : tsupport (χ : X → ℝ) ⊆ ball p (2 * r))
    (c : SobolevSpace μ hQ) (hc : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ)
    (q : Lp ℝ 2 μ) (hq : IsWeakLaplacian μ hQ c q)
    (a : X) {R : ℝ} (hR : 0 < R)
    (hχR : ∀ z ∉ closedBall a R, χ z = 0)
    (hqR : ∀ᵐ z ∂μ, z ∉ closedBall a R → q z = 0)
    (A : Set X) (hA : MeasurableSet A) (hAt : μ A ≠ ∞) (hχA : ∀ z ∈ A, χ z = 1)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (x : X) (lambda : ℝ) :
    ⟪v, (sobolevMeanGram μ hQ U A hA -
      cutoffHeatGram μ hQ hk χ.continuous hχs U hs x lambda) v⟫_ℝ =
      ((μ.real A)⁻¹ * (∫ z in A,
        heatAt μ hQ t (SobolevSpace.toLp μ hQ (G.cutoffEnergy μ hQ χ c)) z ∂μ) -
        kernelHeat μ hQ hk t (SobolevSpace.toLp μ hQ (G.cutoffEnergy μ hQ χ c)) x) -
      lambda * s * ‖v‖ ^ 2 -
      (∫ τ in 0..s, (∫ᵛ z, kernelAverage μ ker τ A z ∂<•(G.cutoffSource μ hQ χ c q))) -
      (∫ τ in s..t, ((∫ᵛ z, kernelAverage μ ker τ A z ∂<•(G.cutoffSource μ hQ χ c q)) -
        (∫ᵛ z, ker τ x z ∂<•(G.cutoffSource μ hQ χ c q)))) := by
  have hfs := cutoffProduct_zero_off μ hQ G.energy c χ hc _ G.bounded hχR
  have hνs := cutoffMeasureSource_variation_compl μ hQ G.energy c q
    (harmonicBochnerSource μ hQ U M κ v) χ hc measurableSet_closedBall hχR hqR
  have hzero : ∀ᵐ z ∂μ, R < dist a z →
      SobolevSpace.toLp μ hQ (G.cutoffEnergy μ hQ χ c) z = 0 := by
    filter_upwards [hfs] with z hz hd
    exact hz (by simpa only [mem_closedBall, dist_comm, not_le] using hd)
  have he := (G.cutoffEnergy_laplacian μ hQ χ hχs hχΩ c hc q hq).average_initial_sub_point_heat_difference μ hQ hk a hR hzero hνs A hA hAt hs hst x
  have hmean : (μ.real A)⁻¹ * (∫ z in A,
      SobolevSpace.toLp μ hQ (G.cutoffEnergy μ hQ χ c) z ∂μ) =
      ⟪v, sobolevMeanGram μ hQ U A hA v⟫_ℝ := by
    rw [sobolevMeanGram_energy]
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (G.cutoffEnergy_coe μ hQ χ hχΩ c hc),
      ae_restrict_mem hA] with z hz hAz
    rw [hz, hχA z hAz, one_mul]
  rw [hmean] at he
  rw [sub_apply, inner_sub_right,
    cutoffHeatGram_kernel_energy μ hQ hk χ.continuous hχs U v
      (G.cutoffEnergy μ hQ χ c) (G.cutoffEnergy_coe μ hQ χ hχΩ c hc)]
  linarith only [he]

end RegularPointCoordinates

end

end OAI
