import OAI.Geometry.RCD.Sobolev.ScalarBochnerConstruction
import OAI.Geometry.RCD.Sobolev.PoissonHessianFromScalar
import OAI.Geometry.RCD.Sobolev.PoissonGradientConstruction
import OAI.Geometry.RCD.Coordinates.CanonicalCoordinateHeatInput
import OAI.Geometry.RCD.Sobolev.HarmonicGradientFromPoisson
import OAI.Geometry.RCD.Harmonic.HarmonicMeanConstruction

namespace OAI

/-! # The local harmonic gradient input from the RCD structure

Nonpositive curvature uses the constructed scalar Bochner estimate.
Positive curvature uses the proved RCD(0,n) reduction; the required
bounded-curvature gradient estimate transfers to the original space.
-/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.harmonicGradientInput_nonpositive {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (hK : K≤0) (p : X) : LocalHarmonicL2GradientInput hX := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  have hscalar := hX.scalarBochner_nonpositive K n hn hK p
  have hess := hX.poisson_hessian_input_of_scalar hn hscalar
  have hpoisson := hX.poissonGradientInput
    (hX.canonicalHeatKernel_isContinuousHeatKernel hn p)
    (hX.canonicalHeatKernel_coordinateBounds hn p) hess
  exact harmonicGradientInput_of_poisson_and_mean hX hpoisson hX.harmonicMeanValueInput

theorem NoncollapsedRCD.harmonicGradientInput {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (p : X) : LocalHarmonicL2GradientInput hX := by
  by_cases hK : K≤0
  · exact hX.harmonicGradientInput_nonpositive hn hK p
  · let h0 := hX.zero_of_nonneg_curvature hn (lt_of_not_ge hK).le
    have hg := h0.harmonicGradientInput_nonpositive hn le_rfl p
    intro hn a τ ha hτ hτ1
    obtain ⟨C,hC,happly⟩ := hg hn a τ ha hτ hτ1
    refine ⟨C,hC,?_⟩
    intro q R hR _
    exact happly q R hR (by simpa only [zero_mul] using neg_nonpos.mpr ha)

end RegularPointCoordinates

end

end OAI
