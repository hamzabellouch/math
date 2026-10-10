import OAI.Geometry.RCD.Harmonic.HarmonicMeanValueInput

namespace OAI

/-! # The local L2 Poincare input used by the Euler forcing

Rajala (2012), Calc. Var. PDE 44, 477--494, Theorem 1.2 supplies the
weak local Poincare inequality. The local doubling bound and the
Sobolev--Poincare consequence in Hajlasz--Koskela (2000), Theorem 5.1,
give this L2 specialization on a smaller ball. Eightfold interior room
is retained; only bounded rescaled curvature is used. The extension from
Lipschitz functions to the canonical Sobolev space is by relaxation.
-/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Only approximation by one constant on an interior ball is retained
from the Sobolev--Poincare inequality. This applies to arbitrary
Sobolev functions, with no harmonic or Euler equation assumed. -/
def LocalMeanPoincareInput {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) : Prop :=
  ∀ κ : ℝ, 0 ≤ κ → ∃ C : ℝ, 1 ≤ C ∧
    ∀ (p : X) (R : ℝ), 0 < R → -κ ≤ K * R ^ 2 →
    ∀ w : SobolevSpace (hausdorff n X) hX.quadratic,
    ∃ k : ℝ, (∫ x in ball p R, (SobolevSpace.toLp (hausdorff n X) hX.quadratic w x - k) ^ 2
      ∂hausdorff n X) ≤ (C * R) ^ 2 *
        ∫ x in ball p (8 * R), localGamma (hausdorff n X) hX.quadratic w w x ∂hausdorff n X

end RegularPointCoordinates

end

end OAI
