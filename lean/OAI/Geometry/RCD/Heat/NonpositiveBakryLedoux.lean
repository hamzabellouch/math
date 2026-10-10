import OAI.Geometry.RCD.Heat.HeatSobolevWeightedBochner
import OAI.Geometry.RCD.Heat.CanonicalKernelConstruction
import OAI.Geometry.RCD.Heat.BakryLedouxInput

namespace OAI

/-! # Bakry--Ledoux from the actual dimensional heat evolution

For nonpositive curvature, the exponential two-time estimate gives the
bounded-weight form with coefficient c(t)=1. This is sufficient for the
scalar Bochner limit in EKS, Definition 4.6 and Theorem 4.8.
-/

open Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.bakryLedoux_nonpositive
    (K : ℝ) (n : ℕ) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (hK : K ≤ 0) {N : ℝ} (hN : (n:ℝ) ≤ N) (p : X) :
    IntegratedBakryLedoux (hausdorff n X) hX.quadratic K N := by
  let μ := hausdorff n X
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  refine ⟨fun _ => 1,tendsto_const_nhds,?_⟩
  intro u d hd w C hw hwC t ht
  have he : -heatGeneratorAt μ hX.quadratic t (SobolevSpace.toLp μ hX.quadratic u) =
      heatAt μ hX.quadratic t d :=
    (heatAt_hasDerivAt μ hX.quadratic t ht (SobolevSpace.toLp μ hX.quadratic u)).unique
      (heat_weakLaplacian_hasDerivAt μ hX.quadratic u d hd ht)
  change -heatGeneratorAt (hausdorff n X) hX.quadratic t
    (SobolevSpace.toLp (hausdorff n X) hX.quadratic u) = heatAt (hausdorff n X) hX.quadratic t d at he
  have hb := hX.heat_weighted_generator_bochner K n hn hK hN
    (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) p u w hw C hwC ht
  rw [he] at hb
  simpa only [mul_one] using hb

end RegularPointCoordinates

end

end OAI
