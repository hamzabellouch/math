import OAI.Geometry.RCD.Heat.HeatMeasureAbsoluteContinuity
import OAI.Geometry.RCD.Heat.HeatMeasureProbability

namespace OAI

/-! # An actual L¹ density for every positive-time heat measure -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology CompactlySupported

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

/-- The Radon--Nikodym density of the constructed heat measure. -/
def heatRadonDensity (t : ℝ) (ht : 0 < t) (x y : X) : ℝ :=
  ((hX.heatRadonMeasure hn p t ht x).rnDeriv (hausdorff n X) y).toReal

omit [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] in
theorem heatRadonDensity_nonneg (t : ℝ) (ht : 0 < t) (x y : X) :
    0 ≤ hX.heatRadonDensity hn p t ht x y := ENNReal.toReal_nonneg

omit [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] in
theorem heatRadonDensity_measurable (t : ℝ) (ht : 0 < t) (x : X) :
    Measurable (hX.heatRadonDensity hn p t ht x) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal

omit [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] in
theorem heatRadonDensity_integrable (t : ℝ) (ht : 0 < t) (x : X) :
    Integrable (hX.heatRadonDensity hn p t ht x) (hausdorff n X) := by
  apply integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv _ _).aemeasurable
  exact (Measure.lintegral_rnDeriv_lt_top _ _).ne

theorem heatRadonDensity_integral_compact (t : ℝ) (ht : 0 < t) (x : X)
    (f : C_c(X, ℝ)) :
    (∫ y, hX.heatRadonDensity hn p t ht x y * f y ∂hausdorff n X) =
      hX.compactHeatEval hn p t ht x f := by
  change (∫ y, ((hX.heatRadonMeasure hn p t ht x).rnDeriv (hausdorff n X) y).toReal * f y
    ∂hausdorff n X) = _
  rw [integral_toReal_rnDeriv_mul (hX.heatRadonMeasure_absolutelyContinuous hn p t ht x)]
  exact hX.heatRadonMeasure_integral hn p t ht x f

theorem heatRadonDensity_integral (t : ℝ) (ht : 0 < t) (x : X) :
    (∫ y, hX.heatRadonDensity hn p t ht x y ∂hausdorff n X) =
      (hX.heatRadonMeasure hn p t ht x).real univ := by
  have h := integral_toReal_rnDeriv_mul
    (hX.heatRadonMeasure_absolutelyContinuous hn p t ht x) (f := fun _ => (1 : ℝ))
  simpa only [heatRadonDensity, mul_one, integral_const, smul_eq_mul, mul_one] using! h

/-- The actual positive-time density has probability mass. -/
theorem heatRadonDensity_mass_one (t : ℝ) (ht : 0 < t) (x : X) :
    (∫ y, hX.heatRadonDensity hn p t ht x y ∂hausdorff n X) = 1 := by
  rw [hX.heatRadonDensity_integral hn p t ht x, hX.heatRadonMeasure_real_mass_one hn p t ht x]

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
