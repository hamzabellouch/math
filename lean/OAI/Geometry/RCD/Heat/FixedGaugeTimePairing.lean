import OAI.Geometry.RCD.Metric.FixedGaugeScaledPotential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace OAI

/-! # The centered interval pairing and the common positive-time gauge -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Interval ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem centered_interval_pairing_eq_fixed_gauge
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (F : C(S, ℝ)) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (z : X) (Ω : Set X) (φ : X → ℝ) (θ : ℝ → ℝ) :
    (∫ t in δ..1, θ t * ∫ x in Ω, φ x *
      (ε * Real.log (∫ a, hX.canonicalHeatKernel hn p (ε*t/2) x a * F a ∂ν)-
        ε * Real.log (hX.compactHeatFactor hn p ν F ε hε z)) ∂hausdorff n X) =
      ∫ t in Ioo δ 1, θ t * ∫ x in Ω,
        φ x*hX.fixedGaugeScaledPotential hn p ν F ε hε δ hδ z t x ∂hausdorff n X := by
  rw [intervalIntegral.integral_of_le hδ1,integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [hX.fixedGaugeScaledPotential_eq hn p ν F ε hε δ hδ z ht.1.le x]
    rfl

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
