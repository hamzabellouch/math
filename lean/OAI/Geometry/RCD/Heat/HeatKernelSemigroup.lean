import OAI.Geometry.RCD.Heat.HeatMarkovKernel
import OAI.Geometry.RCD.Heat.BoundedHeatSemigroup
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

namespace OAI

/-! # Chapman--Kolmogorov for the constructed Markov kernel -/

open Set Filter MeasureTheory Metric TopologicalSpace ProbabilityTheory
open scoped NNReal ENNReal Topology CompactlySupported

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem heatRadonMeasure_integral_compact_semigroup (f : C_c(X, ℝ))
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (x : X) :
    (∫ y, (∫ z, f z ∂hX.heatRadonMeasure hn p t ht y)
      ∂hX.heatRadonMeasure hn p s hs x) =
      ∫ z, f z ∂hX.heatRadonMeasure hn p (s + t) (add_pos hs ht) x := by
  have he (r : ℝ) (hr : 0 < r) (y : X) :
      (∫ z, compactTestToL2 (hausdorff n X) f z ∂hX.heatRadonMeasure hn p r hr y) =
        ∫ z, f z ∂hX.heatRadonMeasure hn p r hr y :=
    integral_congr_ae ((hX.heatRadonMeasure_absolutelyContinuous hn p r hr y).ae_le
      (compactTestToL2_coe (hausdorff n X) f))
  have H := hX.heatRadonMeasure_integral_semigroup hn p
    (compactTestToL2 (hausdorff n X) f) (compactTestToL2_bounded f).choose
    (compactTestToL2_bounded f).choose_spec s t hs ht x
  simpa only [he] using H

/-- The Radon probability family satisfies the measure-valued
Chapman--Kolmogorov law at every starting point. -/
theorem heatMarkovKernel_comp (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    hX.heatMarkovKernel hn p t ht ∘ₖ hX.heatMarkovKernel hn p s hs =
      hX.heatMarkovKernel hn p (s + t) (add_pos hs ht) := by
  apply Kernel.ext
  intro x
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [Kernel.integral_comp f.integrable]
  exact hX.heatRadonMeasure_integral_compact_semigroup hn p f s t hs ht x

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
