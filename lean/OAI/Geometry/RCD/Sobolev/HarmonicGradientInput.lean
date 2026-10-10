import OAI.Geometry.RCD.Coordinates.NormalizedLocalL2

namespace OAI

/-! # The harmonic L² interior gradient specialization

Jiang (2014), JFA266, Theorem 1.1 (arXiv:1307.1334v2, printed p.3),
with eigenvalue zero, gives an interior gradient bound by the local L¹ mean.
Cauchy--Schwarz replaces that mean by the L² mean. Covering a fixed inner
fraction and Bishop--Gromov comparison (Sturm2006II, Theorem2.3) give the
following fixed-fraction specialization. Constants are chosen before the
ball and function and depend only on the stated curvature bound and ratio.
-/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The normalized L² interior gradient bound for harmonic functions.
This is a analytic input, not an affine approximation premise. -/
def LocalHarmonicL2GradientInput {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) : Prop :=
  2 ≤ n → ∀ a τ : ℝ, 0 ≤ a → 0 < τ → τ < 1 →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : X) (R : ℝ), 0 < R → -a ≤ K * R ^ 2 →
      ∀ w : SobolevSpace (hausdorff n X) hX.quadratic,
        IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p R) w →
        ∀ᵐ x ∂(hausdorff n X).restrict (ball p (τ * R)),
          localGamma (hausdorff n X) hX.quadratic w w x ≤
            (C / R) ^ 2 * (((hausdorff n X).real (ball p R))⁻¹ *
              ∫ y in ball p R, (SobolevSpace.toLp (hausdorff n X) hX.quadratic w y) ^ 2
                ∂hausdorff n X)

end RegularPointCoordinates

end

end OAI
