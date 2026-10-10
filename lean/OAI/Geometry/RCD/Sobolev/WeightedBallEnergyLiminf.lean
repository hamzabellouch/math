import OAI.Geometry.RCD.Sobolev.WeightedEnergyLiminf

namespace OAI

/-! # The weighted lower bound on the original physical ball -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.weighted_energy_eventual_lower_on_ball {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n)
    {S ρ τ R : ℝ} (hS : 0<S) (hτ : 0≤τ) (hρτ : ρ<τ)
    (hτR : τ<R) (hRS : R<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (g : Euclidean n → ℝ) (hg : ∀ W<S, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 W))
    (hconv : ∀ W : ℝ, 0<W → W<S → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-g (v k x)|≤δ)
    (φ : Euclidean n →ᵇ ℝ) (hφ : ∀ z, 0≤φ z) (hs : Function.support φ⊆ball 0 ρ)
    {M : ℝ} (hM : 0≤M)
    (hbound : ∀ᶠ k in atTop, ∀ᵐ x ∂(hausdorff n X).restrict (closedBall (p k) (R*r k)),
      r k^2*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x≤M)
    : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      (volume.real (ball (0:Euclidean n) S))⁻¹*(∫ z, φ z*‖fderiv ℝ g z‖^2)-δ≤
        (r k^2/(hausdorff n X).real (ball (p k) (S*r k)))*
          (∫ x in ball (p k) (S*r k), φ (v k x)*localGamma (hausdorff n X) hX.quadratic
            (w k) (w k) x ∂hausdorff n X) := by
  have hlower := hX.weighted_energy_eventual_lower hn hS hτ hρτ hτR hRS
    p r ε v hr hcurv hε hε1 hεlim hv w g hg hconv φ hφ hs hM hbound
  intro δ hδ
  filter_upwards [hlower δ hδ] with k hk
  apply hk.trans
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (sq_nonneg _) ENNReal.toReal_nonneg)
  have hi := (localGamma_memL1 (hausdorff n X) hX.quadratic (w k) (w k)).bdd_mul
    (φ.continuous.measurable.comp (hv k).measurable).aestronglyMeasurable
    (Eventually.of_forall fun x => φ.norm_coe_le_norm (v k x))
  apply setIntegral_mono_set hi.integrableOn
  · filter_upwards [ae_restrict_of_ae (localGamma_self (hausdorff n X) hX.quadratic (w k))] with x hx
    exact mul_nonneg (hφ _) (hx ▸ sq_nonneg _)
  · exact Eventually.of_forall (closedBall_subset_ball (mul_lt_mul_of_pos_right hRS (hr k)))

end RegularPointCoordinates

end

end OAI
