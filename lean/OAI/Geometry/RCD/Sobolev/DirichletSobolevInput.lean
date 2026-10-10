import OAI.Geometry.RCD.Coordinates.NormalizedDistancePoisson
import OAI.Geometry.RCD.Sobolev.AnnularPoincare

namespace OAI

/-!
# The local Sobolev input used by the Poisson construction

Hajlasz--Koskela, *Sobolev met Poincare*, Mem. AMS 145 (2000), no.688,
Theorem5.1 (22)--(23), printed pp.22--23, and Remark3 give local normalized
Sobolev inequalities under local doubling and Poincare. The displayed
specialization uses the RCD local constants at bounded rescaled curvature.
Zero extension from B(r) and the positive annulus B(2r)\B(r) remove the
mean. Only one exponent strictly above two is needed, including n=2.

Zero-boundary coercivity combines with the local Sobolev inequality.
-/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- A fixed superquadratic exponent and normalized zero-boundary Sobolev
constant for small balls with a definite exterior annulus. -/
def LocalDirichletSobolevInput {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) : Prop :=
  2 ≤ n → ∃ d C : ℝ, 1 < d ∧ 0 < C ∧ ∀ (p : X) (r : ℝ),
    0 < r → -1 ≤ K * (64 * r) ^ 2 →
    2 * (hausdorff n X).real (ball p r) ≤ (hausdorff n X).real (ball p (2 * r)) →
    ∀ φ : SobolevSpace.dirichlet (hausdorff n X) hX.quadratic (ball p r),
      (∫ x in ball p r, |SobolevSpace.toLp (hausdorff n X) hX.quadratic φ.val x| ^
        (2 * d) ∂hausdorff n X) ^ (1 / d) ≤
      (C * r ^ 2 * ((hausdorff n X).real (ball p r)) ^ (1 / d - 1)) *
        energyForm (hausdorff n X) hX.quadratic φ.val φ.val

end RegularPointCoordinates

end

end OAI
