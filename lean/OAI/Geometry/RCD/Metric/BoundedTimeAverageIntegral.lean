import OAI.Geometry.RCD.Metric.TimeAverageApproximation
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! # Integrability of bounded time averages against a finite measure -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem bounded_time_average_integrable
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    (f : ℝ → Y → ℝ) (hf : StronglyMeasurable (Function.uncurry f))
    {h t M : ℝ} (hh : 0 < h)
    (hb : ∀ᵐ y ∂ν, ∀ q ∈ Icc (t-h) (t+h), |f q y| ≤ M) :
    Integrable (fun y => timeIntervalAverage (fun q => f q y) h t) ν := by
  let τ := volume.restrict (Icc (t-h) (t+h))
  have hi : Integrable (Function.uncurry f) (τ.prod ν) := by
    apply Integrable.of_bound hf.aestronglyMeasurable M
    have hq : ∀ᵐ p ∂τ.prod ν, p.1 ∈ Icc (t-h) (t+h) :=
      Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually (ae_restrict_mem measurableSet_Icc)
    have hy : ∀ᵐ p ∂τ.prod ν, ∀ q ∈ Icc (t-h) (t+h), |f q p.2| ≤ M :=
      Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually hb
    filter_upwards [hq,hy] with p hp hbp
    exact hbp p.1 hp
  have ha := hi.integral_prod_right.const_mul ((2*h)⁻¹)
  apply ha.congr
  exact Eventually.of_forall fun y => by
    change (2*h)⁻¹*(∫ q, f q y ∂τ) = (2*h)⁻¹*(∫ q in (t-h)..(t+h), f q y)
    rw [intervalIntegral.integral_of_le (by linarith : t-h ≤ t+h),
      ← integral_Icc_eq_integral_Ioc]

end RegularPointCoordinates

end

end OAI
