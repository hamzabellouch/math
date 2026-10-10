import OAI.Analysis.IrrationalRotation.Model.ParameterCircleWeights
import OAI.Analysis.IrrationalRotation.Model.RotationMeasurable
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace OAI

noncomputable section
open MeasureTheory
namespace Invariant233.CircleParameterData

theorem measurableWeight_borel (p : CircleParameterData) (θ : ℝ) :
    Measurable (p.measurableWeight θ) := by
  unfold measurableWeight CircleWeights.weight CircleWeights.cocycle CircleWeights.floorCost
  apply Measurable.exp
  apply Measurable.neg
  apply Measurable.tsum
  intro i
  apply Measurable.mul measurable_const
  apply (measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
  apply Measurable.floor
  apply Measurable.add _ measurable_const
  change Measurable (fun x : Circle =>
    ((AddCircle.equivIco (1 : ℝ) 0 (p.coordFrequency i • x)) : ℝ))
  exact (measurable_subtype_coe.comp
    (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable).comp
      (continuous_const_smul (p.coordFrequency i)).measurable

theorem measurableWeight_operator_bound (p : CircleParameterData) (θ : ℝ)
    (hp : CircleParameterLaws θ p) (x : Circle) :
    ‖(p.measurableWeight θ x : ℂ)‖ ≤ 1 := by
  have hpos : 0 < p.measurableWeight θ x := Real.exp_pos _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  apply Real.exp_le_one_iff.mpr
  apply neg_nonpos.mpr
  apply tsum_nonneg
  intro i
  apply mul_nonneg (hp.C_pos (i.1 + 1) (Nat.succ_le_iff.mpr (Nat.zero_lt_succ _))).le
  apply Int.cast_nonneg
  apply Int.floor_nonneg.mpr
  apply add_nonneg
  · exact (AddCircle.equivIco (1 : ℝ) 0 (p.coordFrequency i • x)).property.1
  · exact mul_nonneg (by norm_num) (Int.fract_nonneg _)

def measurableOperator (p : CircleParameterData) (θ : ℝ)
    (hp : CircleParameterLaws θ p) : Rotation.Hilbert →L[ℂ] Rotation.Hilbert :=
  Rotation.U * Rotation.measurableRepresentation θ
    (fun x => (p.measurableWeight θ x : ℂ)) 1 (by norm_num)
    (Complex.measurable_ofReal.comp (p.measurableWeight_borel θ))
    (p.measurableWeight_operator_bound θ hp)

end Invariant233.CircleParameterData

end

end OAI
