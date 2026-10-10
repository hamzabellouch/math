import OAI.Geometry.RCD.Sobolev.UniformEnergyDensity
import OAI.Geometry.RCD.Sobolev.GradientEnergyFromDensity

namespace OAI

/-! # Integral lower energy bound for the actual local value limit -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.uniform_gradient_energy_lower {K : ℝ} {n : ℕ}
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
    : IntegrableOn (fun z => ‖fderiv ℝ g z‖^2) (ball 0 ρ) volume ∧
      (∫ z in ball 0 ρ, ‖fderiv ℝ g z‖^2)≤
        volume.real (ball (0:Euclidean n) S)*(ν : Measure (Euclidean n)).real (ball 0 ρ) := by
  exact gradient_energy_from_density ν g (ball 0 ρ) ENNReal.toReal_nonneg
    (hX.uniform_energy_density_dominates_gradient hn hS hτ hρτ hτR hRS
      p r ε v hr hcurv hε hε1 hεlim hv w g hg hconv ν henergy)

end RegularPointCoordinates

end

end OAI
