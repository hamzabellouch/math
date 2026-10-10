import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeatContinuous

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile122
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [CompleteSpace X] [SigmaFinite m] in
lemma cheegerHeat_average_tendsto (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m) :
    Tendsto (fun t : ℝ => t⁻¹ • ∫ s in 0..t,cheegerHeat h s u) (𝓝[>] 0) (𝓝 u) := by
  let f (s : ℝ) := cheegerHeat h (max s 0) u
  have hc : Continuous f := by
    apply (cheegerHeat_continuousOn hfin h u).comp_continuous (continuous_id.max continuous_const)
    exact fun s => le_max_right s 0
  have hd := intervalIntegral.integral_hasDerivAt_right
    (f := f) (a := 0) (b := 0) (by simp)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have HH := hd.tendsto_slope_zero_right
  simp only [zero_add,intervalIntegral.integral_same,sub_zero,f,max_self,cheegerHeat_zero,one_apply_eq_self] at HH
  apply HH.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le (le_of_lt ht)] at hs
  dsimp only
  rw [max_eq_left hs.1]
end WeakHessian

end
end InlinedFile122

end OAI
