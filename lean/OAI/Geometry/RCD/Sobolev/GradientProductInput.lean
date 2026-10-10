import OAI.Geometry.RCD.Sobolev.HessianActionInput

namespace OAI

/-! # gradient-product bound on the same local Poisson span

Gigli (2018), Proposition 3.3.22(i), equation (3.3.33), identifies the
gradient of Gamma(f,g) with Hess(f)(grad g,.) + Hess(g)(grad f,.).
Theorem 3.3.8, equation (3.3.18), and Han (2018), Proposition 3.2 and
Theorem 3.3, bound the shifted Hessian square by the full Bochner measure.
Tensor Cauchy--Schwarz and |A+B|^2 <= 2|A|^2+2|B|^2 give the bound below.
The local test-function specialization is Connell et al. (2021), Lemmas
2.6--2.7. Only the n+2-dimensional span already used by the application is
retained.
-/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The gradient-product rule and shifted Hessian bound, using the same
canonical local energy measure as the same local Poisson span.
Locality allows any Sobolev representative of its gradient pairing. -/
def LocalPoissonGradientProductInput {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) : Prop :=
  ∀ κ : ℝ, 0 ≤ κ → -κ ≤ K → ∀ (p : X) (r : ℝ), 0 < r →
    ∀ (L : ℝ≥0)
      (U : Euclidean (n + 2) →L[ℝ] SobolevSpace (hausdorff n X) hX.quadratic)
      (ell : Euclidean (n + 2) →ₗ[ℝ] ℝ),
      (∀ v, IsConstantLaplacianOn (hausdorff n X) hX.quadratic
        (ball p (8 * r)) (U v) (ell v)) →
      (∀ v, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8 * r)),
        localGamma (hausdorff n X) hX.quadratic (U v) (U v) x ≤
          (L : ℝ) ^ 2 * ‖v‖ ^ 2) →
      ∀ M : PositiveBilinearMeasure X (Euclidean (n + 2)),
      (∀ v, Nonempty (LocalHarmonicEnergy (hausdorff n X) hX.quadratic U M κ p r L v)) →
      ∀ t : ℝ, 0 < t → t ≤ 2 * r → ∀ (v w : Euclidean (n + 2))
        (G : SobolevSpace (hausdorff n X) hX.quadratic),
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[
        (hausdorff n X).restrict (ball p t)] localGamma (hausdorff n X) hX.quadratic (U v) (U w)) →
      ∀ b Cv Cw : ℝ, 0 ≤ Cv → 0 ≤ Cw →
      (∀ᵐ x ∂(hausdorff n X).restrict (ball p t),
        localGamma (hausdorff n X) hX.quadratic (U v) (U v) x ≤ Cv ^ 2) →
      (∀ᵐ x ∂(hausdorff n X).restrict (ball p t),
        localGamma (hausdorff n X) hX.quadratic (U w) (U w) x ≤ Cw ^ 2) →
      (∫ x in ball p t,
        localGamma (hausdorff n X) hX.quadratic (G - b • U w) (G - b • U w) x ∂hausdorff n X) ≤
        2 * Cw ^ 2 * ((M.measure v).real (ball p t) -
          (2 * b * ell v - (n : ℝ) * b ^ 2) * (hausdorff n X).real (ball p t)) +
        2 * Cv ^ 2 * (M.measure w).real (ball p t)

end RegularPointCoordinates

end

end OAI
