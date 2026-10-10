import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.ChangeLpLp
import OAI.Geometry.WeakHessian.Sobolev.UpperGradientNormTendsto

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open scoped Topology
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m ν : Measure X}

lemma cheegerEnergy_eq_of_comparable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] (hfinite : FiniteOnBoundedSets m)
    {C E : ℝ≥0} (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (E : ℝ≥0∞) • m)
    {f D : Lp ℝ 2 m} (hD : IsMinimalLocalWeakUpperGradient m (f : X → ℝ) D)
    (henergy : cheegerEnergy m (f : X → ℝ) = ENNReal.ofReal (‖D‖^2/2)) :
    cheegerEnergy ν (f : X → ℝ) =
      ENNReal.ofReal (‖Lp.LpToLpOfMeasureLeSMul ENNReal.coe_ne_top hν D‖^2/2) := by
  let T : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 ν := Lp.LpToLpOfMeasureLeSMul ENNReal.coe_ne_top hν
  obtain ⟨fs,hLip,hfs,hDs,hf,hG⟩ := exists_lipschitz_strong_slopes hfinite hD henergy
  have hfn := tendsto_toLp_changeMeasure ENNReal.coe_ne_top hν hfs (Lp.memLp f)
    (by simpa only [Lp.toLp_coeFn] using hf)
  have hDn := tendsto_toLp_changeMeasure ENNReal.coe_ne_top hν hDs (Lp.memLp D)
    (by simpa only [Lp.toLp_coeFn] using hG)
  have hDf : ((Lp.memLp D).of_measure_le_smul ENNReal.coe_ne_top hν).toLp (D : X → ℝ) = T D := rfl
  rw [hDf] at hDn
  have he : Tendsto (fun n => (2 : ℝ≥0∞)⁻¹ *
      ∫⁻ x, (localSlope (fs n) x)^2 ∂ν) atTop (𝓝 (ENNReal.ofReal (‖T D‖^2/2))) := by
    have H := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hDn.norm.pow 2).div_const 2)
    convert H using 1
    funext n
    exact half_lintegral_localSlope_eq (hLip n).choose_spec
      ((hDs n).of_measure_le_smul ENNReal.coe_ne_top hν)
  have hle : cheegerEnergy ν (f : X → ℝ) ≤ ENNReal.ofReal (‖T D‖^2/2) := by
    have H := cheegerEnergy_le_liminf
      ((Lp.memLp f).of_measure_le_smul ENNReal.coe_ne_top hν)
      (fun n => ⟨hLip n,(hfs n).of_measure_le_smul ENNReal.coe_ne_top hν⟩)
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fs
        (fun n => (hfs n).of_measure_le_smul ENNReal.coe_ne_top hν)
        (f : X → ℝ) ((Lp.memLp f).of_measure_le_smul ENNReal.coe_ne_top hν)).mp hfn)
    rwa [he.liminf_eq] at H
  have hDν : IsMinimalLocalWeakUpperGradient ν (f : X → ℝ) (T D) :=
    (hD.change_measure hm hν).congr_ae Filter.EventuallyEq.rfl
      (Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.coe_ne_top hν D).symm
  obtain ⟨D',hD',hlo⟩ := exists_minimalGradient_energy_le_cheeger
    (hfinite.of_measure_le_smul ENNReal.coe_ne_top hν)
    ((Lp.memLp f).of_measure_le_smul ENNReal.coe_ne_top hν)
    (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)
  have heq : D' = T D := Lp.ext (hD'.ae_eq hDν)
  rw [heq] at hlo
  exact le_antisymm hle hlo

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end

end OAI
