import OAI.Geometry.RCD.Heat.HeatKernelRows
import OAI.Geometry.RCD.Coordinates.WeightedBilinearMeasure

namespace OAI

/-!
# Compactly supported measure Laplacians and continuous Sobolev tests

`IsMeasureLaplacian` records the distributional integration-by-parts identity
on continuous compactly supported Sobolev tests. It is a definition, not an
existence assumption. The cutoff argument extends this identity to arbitrary
continuous Sobolev representatives when the function and its full signed
Laplacian have compact support. In particular it applies to positive-time
kernel rows without removing singular mass.
-/

open Set MeasureTheory
open scoped InnerProductSpace BoundedContinuousFunction NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The weak measure-valued Laplacian, tested on continuous compactly
supported Sobolev representatives. -/
def IsMeasureLaplacian (u : SobolevSpace μ hQ) (ν : SignedMeasure X) : Prop :=
  ∀ (φ : SobolevSpace μ hQ) (v : X → ℝ), Continuous v → HasCompactSupport v →
    SobolevSpace.toLp μ hQ φ =ᵐ[μ] v →
      energyForm μ hQ u φ = -(∫ᵛ x, v x ∂<•ν)

/-- Compact support of both the function and the full signed source allows
all continuous Sobolev representatives as tests. -/
theorem IsMeasureLaplacian.test_continuous
    {u : SobolevSpace μ hQ} {ν : SignedMeasure X}
    (hν : IsMeasureLaplacian μ hQ u ν) (c : X) {R : ℝ} (hR : 0 < R)
    (hu : ∀ᵐ x ∂μ, R < dist c x → SobolevSpace.toLp μ hQ u x = 0)
    (hsν : ν.variation (Metric.closedBall c R)ᶜ = 0)
    (φ : SobolevSpace μ hQ) {v : X → ℝ} (hv : Continuous v)
    (hφ : SobolevSpace.toLp μ hQ φ =ᵐ[μ] v) :
    energyForm μ hQ u φ = -(∫ᵛ x, v x ∂<•ν) := by
  let η := radialCutoff c R
  have hη : LipschitzWith _ η := radialCutoff_lipschitz c hR
  have hsη : HasCompactSupport η := radialCutoff_hasCompactSupport c hR
  have hbη (x : X) : |η x| ≤ ((1 : ℝ≥0) : ℝ) := by
    rw [abs_of_nonneg (radialCutoff_bounds c R x).1]
    exact (radialCutoff_bounds c R x).2
  have hnη (x : X) : 0 ≤ η x := (radialCutoff_bounds c R x).1
  let ψ := SobolevSpace.cutoffCLM μ hQ hη hsη hbη hnη φ
  have hψ : SobolevSpace.toLp μ hQ ψ =ᵐ[μ] fun x => η x * v x := by
    filter_upwards [SobolevSpace.cutoffCLM_coe μ hQ hη hsη hbη hnη φ, hφ] with x hx he
    exact hx.trans (by rw [he])
  have hg : localGamma μ hQ u ψ =ᵐ[μ] localGamma μ hQ u φ := by
    filter_upwards [localGamma_eq_on_eq μ hQ ψ φ u,
      localGamma_comm μ hQ u ψ, localGamma_comm μ hQ u φ,
      localGamma_zero_on_level μ hQ u ψ 0, localGamma_zero_on_level μ hQ u φ 0,
      hψ, hφ, hu] with x he hc hc' hz hz' hx hx' hux
    by_cases hin : dist c x ≤ R
    · rw [hc, hc']
      apply he
      rw [hx, hx']
      change radialCutoff c R x * v x = v x
      rw [radialCutoff_eq_one c hR hin, one_mul]
    · rw [hz (hux (lt_of_not_ge hin)), hz' (hux (lt_of_not_ge hin))]
  have henergy : energyForm μ hQ u ψ = energyForm μ hQ u φ := by
    rw [← integral_localGamma_eq_energyForm, ← integral_localGamma_eq_energyForm]
    exact integral_congr_ae hg
  have hae : (fun x => η x * v x) =ᵐ[ν.variation] v := by
    have hm : ∀ᵐ x ∂ν.variation, x ∈ Metric.closedBall c R :=
      ae_iff.mpr hsν
    filter_upwards [hm] with x hx
    change radialCutoff c R x * v x = v x
    rw [radialCutoff_eq_one c hR (by simpa only [Metric.mem_closedBall, dist_comm] using hx), one_mul]
  have he := hν ψ (fun x => η x * v x) (hη.continuous.mul hv) hsη.mul_right hψ
  rw [henergy, VectorMeasure.integral_congr_ae hae] at he
  exact he

variable [μ.Regular] {p : ℝ → X → X → ℝ} (hp : IsContinuousHeatKernel μ hQ p)

/-- Integration by parts against the actual continuous heat-kernel row. -/
theorem IsMeasureLaplacian.test_heatKernel
    {u : SobolevSpace μ hQ} {ν : SignedMeasure X}
    (hν : IsMeasureLaplacian μ hQ u ν) (c : X) {R : ℝ} (hR : 0 < R)
    (hu : ∀ᵐ x ∂μ, R < dist c x → SobolevSpace.toLp μ hQ u x = 0)
    (hsν : ν.variation (Metric.closedBall c R)ᶜ = 0)
    {t : ℝ} (ht : 0 < t) (x : X) :
    energyForm μ hQ u (heatKernelSobolev μ hQ hp t ht x) =
      -(∫ᵛ z, p t x z ∂<•ν) :=
  hν.test_continuous μ hQ c hR hu hsν _ (hp.continuous_right t ht x)
    (heatKernelSobolev_coe μ hQ hp ht x)

end RegularPointCoordinates

end

end OAI
