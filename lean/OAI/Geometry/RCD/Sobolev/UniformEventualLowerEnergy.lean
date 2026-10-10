import OAI.Geometry.RCD.Sobolev.UniformLowerEnergyFromSequence

namespace OAI

/-! # Lower energy bounds after discarding a finite initial segment -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.gradient_energy_lower_of_curvature_eventual_sequence {K : ℝ} {n : ℕ}
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
    {M C : ℝ} (hM : 0≤M)
    (hbound : ∀ᶠ k in atTop, ∀ᵐ x ∂(hausdorff n X).restrict (closedBall (p k) (R*r k)),
      r k^2*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x≤M)
    (hupper : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      (r k^2/(hausdorff n X).real (ball (p k) (S*r k)))*
        (∫ x in closedBall (p k) (R*r k), localGamma (hausdorff n X) hX.quadratic
          (w k) (w k) x ∂hausdorff n X)≤C+δ) :
    IntegrableOn (fun z => ‖fderiv ℝ g z‖^2) (ball 0 ρ) volume ∧
      (∫ z in ball 0 ρ, ‖fderiv ℝ g z‖^2)≤volume.real (ball (0:Euclidean n) S)*C := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hbound
  apply hX.gradient_energy_lower_of_curvature_sequence hn hS hτ hρτ hτR hRS
    (fun k => p (k+N)) (fun k => r (k+N)) (fun k => ε (k+N)) (fun k => v (k+N))
    (fun k => hr (k+N)) (fun k => hcurv (k+N))
    (fun k => hε (k+N)) (fun k => hε1 (k+N)) (hεlim.comp (tendsto_add_atTop_nat N))
    (fun k => hv (k+N)) (fun k => w (k+N)) g hg
    (fun W hW hWS δ hδ => (tendsto_add_atTop_nat N).eventually (hconv W hW hWS δ hδ))
    hM (fun k => hN (k+N) (Nat.le_add_left N k))
    (fun δ hδ => (tendsto_add_atTop_nat N).eventually (hupper δ hδ))

end RegularPointCoordinates

end

end OAI
