import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.CutoffCheegerEnergy
import OAI.Geometry.WeakHessian.Measure.RadialCutoff
import OAI.Geometry.WeakHessian.LocalBounds.BoundedMulLpTendsto

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace WeakHessian
open WeakHessianFunctional MeasureTheory Set Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma CurvatureDimension.global_cheegerEnergy_le_weak {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfinite : FiniteOnBoundedSets m) (o : X)
    {f W : Lp ℝ 2 m} (hf : IsLocalWeakUpperGradient m (f : X → ℝ) (W : X → ℝ)) :
    cheegerEnergy m (f : X → ℝ) ≤ ENNReal.ofReal (‖W‖^2/2) := by
  by_cases hm : m = 0
  · have hae : (f : X → ℝ) =ᵐ[m] (fun _ => (0:ℝ)) := by
      subst m
      change ∀ᶠ x in MeasureTheory.ae (0 : Measure X), (f : X → ℝ) x = 0
      rw [MeasureTheory.ae_zero]
      exact Filter.eventually_bot
    rw [cheegerEnergy_congr_ae hae,cheegerEnergy_zero]
    exact bot_le
  obtain ⟨ν,hνp,hνm,hmν,⟨C,hC⟩,hlocal⟩ := exists_probability_reference m o hm hfinite
  let : IsProbabilityMeasure ν := hνp
  let L : ℕ → ℝ≥0 := fun n => ((n:ℝ≥0)+1)⁻¹
  have hφB (n : ℕ) (x : X) : |radialCutoff o n x| ≤ 1 := by
    rw [abs_of_nonneg (radialCutoff_nonneg o n x)]
    exact radialCutoff_le_one o n x
  let u : ℕ → Lp ℝ 2 m := fun n => boundedMulLp
    (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable (ae_of_all m (hφB n)) f
  have hu : Tendsto u atTop (𝓝 f) := boundedMulLp_tendsto
    (fun n => (radialCutoff_lipschitz o n).continuous.aestronglyMeasurable)
    (fun n => ae_of_all m (hφB n)) (ae_of_all m (radialCutoff_tendsto o)) f
  have hL : Tendsto (fun n => (L n:ℝ)) atTop (𝓝 0) := by
    simpa only [L,NNReal.coe_inv,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one,one_div]
      using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hb : Tendsto (fun n => ENNReal.ofReal ((‖W‖+(L n:ℝ)*‖f‖)^2/2)) atTop
      (𝓝 (ENNReal.ofReal (‖W‖^2/2))) := by
    have H := (((tendsto_const_nhds (x := ‖W‖)).add (hL.mul_const ‖f‖)).pow 2).div_const 2
    simpa only [zero_mul,add_zero] using ENNReal.tendsto_ofReal H
  change (f, ENNReal.ofReal (‖W‖^2/2)) ∈
    {p : Lp ℝ 2 m × ℝ≥0∞ | cheegerEnergy m (p.1 : X → ℝ) ≤ p.2}
  apply lowerSemicontinuous_cheegerEnergy.isClosed_epigraph.mem_of_tendsto (hu.prodMk_nhds hb)
  apply Eventually.of_forall
  intro n
  obtain ⟨c,hc⟩ := hlocal (tsupport (radialCutoff o n)) (radialCutoff_compact o n).isBounded
  exact hcd.cutoff_cheegerEnergy_le hC hmν hf (radialCutoff_lipschitz o n)
    (radialCutoff_compact o n) (radialCutoff_nonneg o n) (radialCutoff_le_one o n)
    ENNReal.coe_ne_top hc
end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
