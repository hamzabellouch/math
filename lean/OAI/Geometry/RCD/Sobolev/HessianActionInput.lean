import OAI.Geometry.RCD.Sobolev.LocalHessianAction
import OAI.Geometry.RCD.Sobolev.PoissonHessianInput

namespace OAI

/-! # finite-span Hessian action bounds

Gigli, arXiv:1407.0809v1, equation (3.1.9), p. 99, and Theorem 3.3.8,
equations (3.3.18)--(3.3.19), p. 110, give the three-term Hessian action
and its Hilbert--Schmidt bound. Han, JGA 28 (2018), Proposition 3.2,
p. 1302, and Theorem 3.3, p. 1305, give the top-dimensional trace identity
and the strengthened Bochner inequality on every local-dimensional stratum.
Completing the trace-defect square gives the shifted-square bound also
when the local dimension is less than n. Tensor Cauchy--Schwarz then gives
the displayed product of the two direction bounds.

This input retains only the n+2-dimensional local Poisson span. It is
separate from the integrated Hessian input, because the commutator needs
actions in arbitrary gradient directions, not only zero-boundary tests.
-/

open Set Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The local Hessian action specialization needed for the
two-center commutator, using the same full Bochner measure at every radius. -/
def LocalPoissonHessianActionInput {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) : Prop :=
  ∀ κ : ℝ, 0 ≤ κ → -κ ≤ K → ∀ (p : X) (r : ℝ), 0 < r →
    ∀ (L : ℝ≥0)
      (U : Euclidean (n + 2) →L[ℝ] SobolevSpace (hausdorff n X) hX.quadratic)
      (ell : Euclidean (n + 2) →ₗ[ℝ] ℝ),
      (∀ v, IsConstantLaplacianOn (hausdorff n X) hX.quadratic
        (ball p (8 * r)) (U v) (ell v)) →
      (∀ v, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8 * r)),
        localGamma (hausdorff n X) hX.quadratic (U v) (U v) x ≤
          (L : ℝ) ^ 2 * ‖v‖ ^ 2) →
      ∃ M : PositiveBilinearMeasure X (Euclidean (n + 2)),
        (∀ v, Nonempty (LocalHarmonicEnergy (hausdorff n X) hX.quadratic U M κ p r L v)) ∧
        ShiftedBochnerLowerBound M ((hausdorff n X).restrict (ball p (2 * r))) ell n ∧
        ∀ t : ℝ, 0 < t → t ≤ 2 * r →
          ∃ G : ∀ v w, LocalHessianPairing (hausdorff n X) hX.quadratic (ball p t) (U v) (U w),
          ∀ v w z (b : ℝ),
            let H := localHessianAction (hausdorff n X) hX.quadratic (U v) (U w) (U z)
              (G v w).mixed (G v z).mixed (G w z).mixed
            MemLp (fun x => H x - b * localGamma (hausdorff n X) hX.quadratic (U w) (U z) x)
              2 ((hausdorff n X).restrict (ball p t)) ∧
            ∀ Cw Cz : ℝ, 0 ≤ Cw → 0 ≤ Cz →
            (∀ᵐ x ∂(hausdorff n X).restrict (ball p t),
              localGamma (hausdorff n X) hX.quadratic (U w) (U w) x ≤ Cw ^ 2) →
            (∀ᵐ x ∂(hausdorff n X).restrict (ball p t),
              localGamma (hausdorff n X) hX.quadratic (U z) (U z) x ≤ Cz ^ 2) →
            (∫ x in ball p t,
              (H x - b * localGamma (hausdorff n X) hX.quadratic (U w) (U z) x) ^ 2
                ∂hausdorff n X) ≤
              (Cw ^ 2 * Cz ^ 2) *
                ((M.measure v).real (ball p t) -
                  (2 * b * ell v - (n : ℝ) * b ^ 2) * (hausdorff n X).real (ball p t))

end RegularPointCoordinates

end

end OAI
