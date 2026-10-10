import OAI.Geometry.RCD.Sobolev.UniformEnergyDerivative

namespace OAI

/-! # One full-measure set for the local gradient-energy comparison -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.uniform_energy_density_dominates_gradient {K : ℝ} {n : ℕ}
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
    (ν : FiniteMeasure (Euclidean n))
    (henergy : Tendsto (fun k => (localEnergyMeasure (hausdorff n X) hX.quadratic (w k)
      (closedBall (p k) (R*r k))
      (r k^2/(hausdorff n X).real (ball (p k) (S*r k)))).map (v k)) atTop (𝓝 ν))
    : ∀ᵐ z ∂(volume : Measure (Euclidean n)).restrict (ball 0 ρ),
      ‖fderiv ℝ g z‖^2≤volume.real (ball (0:Euclidean n) S)*
        ((ν : Measure (Euclidean n)).rnDeriv volume z).toReal := by
  apply (ae_restrict_iff' measurableSet_ball).mpr
  filter_upwards [euclidean_energy_density_limit ν] with z hz hzmem
  by_cases hd : DifferentiableAt ℝ g z
  · apply hX.uniform_energy_density_dominates_derivative hn hS hτ hρτ hτR hRS
      p r ε v hr hcurv hε hε1 hεlim hv w g hg hconv ν henergy z
    · simpa only [mem_ball,dist_zero_right] using hzmem
    · exact hd.hasFDerivAt
    · exact hz
  · rw [fderiv_zero_of_not_differentiableAt hd,norm_zero,zero_pow (by decide : 2≠0)]
    exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

end RegularPointCoordinates

end

end OAI
