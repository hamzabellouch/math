import OAI.Geometry.RCD.Harmonic.HarmonicOperatorEvolution
import OAI.Geometry.RCD.Harmonic.IntegratedPolarization
import OAI.Geometry.RCD.Heat.KernelDensityTime

namespace OAI

/-! # Exact quadratic identities for the averaged cutoff error -/

open Set Metric MeasureTheory Filter
open scoped InnerProductSpace NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The actual product-rule source is supported in the closed outer ball. -/
theorem GoodLaplacianCutoff.error_zero_off_outerBall {p : X} {ρ C : ℝ}
    (χ : GoodLaplacianCutoff μ hQ p ρ C) (u : SobolevSpace μ hQ) :
    ∀ᵐ z ∂μ, z ∉ closedBall p (2 * ρ) →
      cutoffSourceDensity μ hQ u χ.sobolev χ.laplacian z = 0 := by
  filter_upwards [χ.error_zero_off_annulus μ hQ u] with z hz hn
  apply hz
  intro h
  exact hn (by simpa only [mem_closedBall, dist_comm] using h.2)

variable [μ.Regular] [IsLocallyFiniteMeasure μ]
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)
  {n : ℕ} {U : Euclidean n →L[ℝ] SobolevSpace μ hQ}
  {M : PositiveBilinearMeasure X (Euclidean n)} {κ : ℝ} {p : X} {r : ℝ} {L : ℝ≥0}
  (G : ∀ v, LocalHarmonicEnergy μ hQ U M κ p r L v)
  {ρ C : ℝ} (χ : GoodLaplacianCutoff μ hQ p ρ C)

include hk in
/-- The averaged error is quadratic in every direction; this follows from
the actual pointwise heat equation and Fubini, not an extra quadraticity input. -/
theorem averaged_cutoff_error_energy (hρ : 0 < ρ) (hρr : ρ < r)
    {t : ℝ} (ht : 0 < t) (A : Set X) (hA : MeasurableSet A)
    (hbounded : Bornology.IsBounded A) (v : Euclidean n) :
    ⟪v, polarizedDerivative (fun w => ∫ z, kernelAverage μ ker t A z *
      cutoffSourceDensity μ hQ (G w).energy χ.sobolev χ.laplacian z ∂μ) v⟫_ℝ =
      ∫ z, kernelAverage μ ker t A z *
        cutoffSourceDensity μ hQ (G v).energy χ.sobolev χ.laplacian z ∂μ := by
  let B := fun x => harmonicHeatError μ hQ (k := ker) G χ t x
  let d := fun w z => cutoffSourceDensity μ hQ (G w).energy χ.sobolev χ.laplacian z
  have hi (w : Euclidean n) : Integrable (d w) μ := cutoffSourceDensity_integrable μ hQ _ _ _
  have hz (w : Euclidean n) : ∀ᵐ z ∂μ, z ∉ closedBall p (2 * ρ) → d w z = 0 :=
    χ.error_zero_off_outerBall μ hQ _
  have hb (w : Euclidean n) (x : X) : ⟪w, B x w⟫_ℝ = ∫ z, ker t x z * d w z ∂μ :=
    harmonicHeatError_energy μ hQ hk G χ hρ hρr ht x w
  have hint (w : Euclidean n) : Integrable (fun x => ⟪w, B x w⟫_ℝ) (μ.restrict A) := by
    have hc := kernel_integral_density_continuous μ hQ hk ht (hi w)
      (isCompact_closedBall p (2 * ρ)) (hz w)
    have hcA := (hc.locallyIntegrable (μ := μ)).integrableOn_isCompact
      (Metric.isCompact_of_isClosed_isBounded isClosed_closure hbounded.closure)
    exact (hcA.mono_set subset_closure).congr (Eventually.of_forall fun x => (hb w x).symm)
  have he (w : Euclidean n) : (∫ z, kernelAverage μ ker t A z * d w z ∂μ) =
      (μ.real A)⁻¹ * ∫ x in A, ⟪w, B x w⟫_ℝ ∂μ := by
    rw [kernelAverage_integral_density μ hQ hk ht A hA hbounded (hi w)
      (isCompact_closedBall p (2 * ρ)) (hz w)]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun x => (hb w x).symm)
  have hB (x : X) : (B x).IsSymmetric := polarizedDerivative_isSymmetric _
  change ⟪v, polarizedDerivative (fun w => ∫ z, kernelAverage μ ker t A z * d w z ∂μ) v⟫_ℝ = _
  rw [funext he, polarizedDerivative_smul, smul_apply, inner_smul_right,
    integrated_polarization_energy (μ.restrict A) B hB hint, ← he]

include hk in
/-- The averaged-minus-pointwise source pairing is likewise the quadratic
form of its finite polarization. -/
theorem difference_cutoff_error_energy (hρ : 0 < ρ) (hρr : ρ < r)
    {t : ℝ} (ht : 0 < t) (A : Set X) (hA : MeasurableSet A)
    (hbounded : Bornology.IsBounded A) (x : X) (v : Euclidean n) :
    ⟪v, polarizedDerivative (fun w => ∫ z, (kernelAverage μ ker t A z - ker t x z) *
      cutoffSourceDensity μ hQ (G w).energy χ.sobolev χ.laplacian z ∂μ) v⟫_ℝ =
      ∫ z, (kernelAverage μ ker t A z - ker t x z) *
        cutoffSourceDensity μ hQ (G v).energy χ.sobolev χ.laplacian z ∂μ := by
  let d := fun w z => cutoffSourceDensity μ hQ (G w).energy χ.sobolev χ.laplacian z
  have he (w : Euclidean n) : (∫ z, (kernelAverage μ ker t A z - ker t x z) * d w z ∂μ) =
      (∫ z, kernelAverage μ ker t A z * d w z ∂μ) - ∫ z, ker t x z * d w z ∂μ := by
    have hi : Integrable (d w) μ := cutoffSourceDensity_integrable μ hQ _ _ _
    have hz := χ.error_zero_off_outerBall μ hQ (G w).energy
    simp_rw [sub_mul]
    exact integral_sub
      (continuous_mul_integrable_compact μ
        (kernelAverage_continuous μ hQ hk ht hA hbounded) hi (isCompact_closedBall p (2 * ρ)) hz)
      (continuous_mul_integrable_compact μ
        (hk.continuous_right t ht x) hi (isCompact_closedBall p (2 * ρ)) hz)
  change ⟪v, polarizedDerivative (fun w => ∫ z, (kernelAverage μ ker t A z - ker t x z) * d w z ∂μ) v⟫_ℝ = _
  rw [funext he, polarizedDerivative_sub, sub_apply, inner_sub_right,
    averaged_cutoff_error_energy μ hQ hk G χ hρ hρr ht A hA hbounded]
  change _ - ⟪v, harmonicHeatError μ hQ (k := ker) G χ t x v⟫_ℝ = _
  rw [harmonicHeatError_energy μ hQ hk G χ hρ hρr ht]
  exact (he v).symm

end RegularPointCoordinates

end

end OAI
