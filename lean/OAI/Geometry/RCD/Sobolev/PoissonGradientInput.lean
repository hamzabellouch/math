import OAI.Geometry.RCD.Sobolev.ConstantLaplacianBochnerInput

namespace OAI

/-!
# interior gradient input for the Poisson replacements

Jiang, *Cheeger-harmonic functions in metric measure spaces revisited*,
J. Funct. Anal. 266 (2014), 1373--1394, Theorem 3.1 (arXiv:1307.1334v2,
printed p.7), bounds the gradient by the local supremum of the function
and the bounded right-hand side. The following is only its constant-source
interior-ball consequence on RCD spaces at bounded rescaled curvature.
The half-radius conclusion follows by covering with the theorem's
one-eighth-radius balls. RCD supplies the uniform local doubling, Poincare
and heat-semigroup curvature constants.
-/

open Set Metric MeasureTheory

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The constant-Laplacian, bounded-value specialization of Jiang2014,
Theorem3.1, with one constant uniform at bounded rescaled curvature. -/
def LocalPoissonGradientInput {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) : Prop :=
  2 ≤ n → ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : X) (r : ℝ), 0 < r → -1 ≤ K * r ^ 2 →
    ∀ (f : SobolevSpace (hausdorff n X) hX.quadratic) (c A : ℝ), 0 ≤ A →
      IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p (8 * r)) f c →
      (∀ᵐ x ∂(hausdorff n X).restrict (ball p (8 * r)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic f x| ≤ A) →
      ∀ᵐ x ∂(hausdorff n X).restrict (ball p (4 * r)),
        localGamma (hausdorff n X) hX.quadratic f f x ≤
          (C * (A / r + |c| * r)) ^ 2

end RegularPointCoordinates

end

end OAI
