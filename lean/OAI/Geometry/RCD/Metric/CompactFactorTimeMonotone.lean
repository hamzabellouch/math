import OAI.Geometry.RCD.Heat.KernelHeatTimeMonotone
import OAI.Geometry.RCD.Metric.CompactFactorNonnegativeData

namespace OAI

/-! # A time comparison independent of the compact endpoint factor -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2≤n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_factor_log_time_lower (hK : K≤0)
    {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0≤ρ x) {C : ℝ≥0}
    (hC : ∀ᵐ x ∂hausdorff n X, |ρ x|≤C)
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : C(S, ℝ)) (hF : ∀ a, 0<F a) {a b : ℝ}
    (ha : 0<a) (hab : a≤b) (x : X) :
    Real.log (hX.compactHeatFactor hn p ν F a ha x)-
      Real.log (hX.compactHeatFactor hn p ν F b (ha.trans_le hab) x) ≤
      (n:ℝ)*(Real.log b-Real.log a+|K| *(b-a)) := by
  obtain ⟨f,hf0,⟨A,hA⟩,he⟩ :=
    hX.compact_heat_factor_nonnegative_data hn p ν ρ hρ hρ0 hC hν F hF
  have hh := hX.kernelHeat_time_monotone hn p hK
    (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) f hf0 A hA ha hab x
  rw [←he a ha x,←he b (ha.trans_le hab) x] at hh
  have ha0 := hX.compactHeatFactor_positive hn p ν F hF a ha x
  have hb0 := hX.compactHeatFactor_positive hn p ν F hF b (ha.trans_le hab) x
  have hl := Real.log_le_log (mul_pos (Real.exp_pos _) ha0) hh
  rw [Real.log_mul (Real.exp_ne_zero _) ha0.ne',
    Real.log_mul (Real.exp_ne_zero _) hb0.ne',Real.log_exp,Real.log_exp] at hl
  nlinarith only [hl]

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
