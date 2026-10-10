import OAI.Geometry.RCD.Sobolev.LocalPoissonGradientMeasure
import OAI.Geometry.RCD.Sobolev.BochnerTestForm

namespace OAI

/-! # Actual scalar energy measures on the finite Poisson span -/

open Set Filter MeasureTheory Metric
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.poisson_scalar_energy_family {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (κ : ℝ) (hK : -κ ≤ K) (p : X) {r : ℝ} (hr : 0 < r) (L : ℝ≥0)
    (U : Euclidean (n + 2) →L[ℝ] SobolevSpace (hausdorff n X) hX.quadratic)
    (ell : Euclidean (n + 2) →ₗ[ℝ] ℝ)
    (hU : ∀ v, IsConstantLaplacianOn (hausdorff n X) hX.quadratic
      (ball p (8 * r)) (U v) (ell v))
    (hL : ∀ v, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8 * r)),
      localGamma (hausdorff n X) hX.quadratic (U v) (U v) x ≤ (L : ℝ) ^ 2 * ‖v‖ ^ 2) :
    ∃ (G : Euclidean (n + 2) → SobolevSpace (hausdorff n X) hX.quadratic)
      (σ : Euclidean (n + 2) → Measure X),
      (∀ v, IsFiniteMeasure (σ v)) ∧
      (∀ v, ∀ᵐ x ∂hausdorff n X, 0 ≤ SobolevSpace.toLp (hausdorff n X) hX.quadratic (G v) x ∧
        SobolevSpace.toLp (hausdorff n X) hX.quadratic (G v) x ≤ (L : ℝ) ^ 2 * ‖v‖ ^ 2) ∧
      (∀ v, SobolevSpace.toLp (hausdorff n X) hX.quadratic (G v)
        =ᵐ[(hausdorff n X).restrict (ball p (5 * r / 2))]
          localGamma (hausdorff n X) hX.quadratic (U v) (U v)) ∧
      (∀ v (ψ : SobolevSpace (hausdorff n X) hX.quadratic) (f : X → ℝ),
        Continuous f → HasCompactSupport f → tsupport f ⊆ ball p (5 * r / 2) →
        SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ =ᵐ[hausdorff n X] f →
        bochnerTestForm (hausdorff n X) hX.quadratic κ (G v) ψ = ∫ x, f x ∂σ v) := by
  have hscalar (v : Euclidean (n + 2)) := hX.local_poisson_energy_measure hn (U v) (ell v)
    (p := p) (R := 5 * r / 2) (b := 8 * r) (by positivity) (by linarith)
    (hU v) (L * ‖v‖₊) (by
      simpa only [NNReal.coe_mul, coe_nnnorm, mul_pow] using hL v) κ hK
  choose G σ hσ hG hrep hΔ using hscalar
  refine ⟨G, σ, hσ, ?_, hrep, ?_⟩
  · intro v
    simpa only [NNReal.coe_mul, coe_nnnorm, mul_pow] using hG v
  · intro v ψ f hf hs hfs hψ
    have : IsFiniteMeasure (σ v) := hσ v
    exact bochnerTestForm_of_measure_laplacian (hausdorff n X) hX.quadratic measurableSet_ball
      (U v) (G v) κ (σ v) (hrep v) (hΔ v) ψ f hf hs hfs hψ

end RegularPointCoordinates

end

end OAI
