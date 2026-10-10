import Mathlib.Analysis.SpecialFunctions.Complex.Circle

namespace OAI

/-! Elementary argument in turns on the punctured complex plane. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

def normalizedArgument (z : ℂ) : UnitAddCircle :=
  AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero (Complex.arg z : Real.Angle)

theorem normalizedArgument_eq (z : ℂ) :
    normalizedArgument z = (Complex.arg z / (2 * Real.pi) : ℝ) := by
  change ((Complex.arg z * ((2 * Real.pi)⁻¹ * 1) : ℝ) : UnitAddCircle) = _
  congr 1
  simp only [mul_one, div_eq_mul_inv]

theorem continuousAt_normalizedArgument {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt normalizedArgument z :=
  ((AddCircle.continuous_equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero).continuousAt).comp
    (Complex.continuousAt_arg_coe_angle hz)

theorem normalizedArgument_mul {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    normalizedArgument (z * w) = normalizedArgument z + normalizedArgument w := by
  let e : Real.Angle ≃+ UnitAddCircle :=
    AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero
  change e (Complex.arg (z * w) : Real.Angle) = e (Complex.arg z) + e (Complex.arg w)
  rw [Complex.arg_mul_coe_angle hz hw]
  exact e.map_add _ _

theorem normalizedArgument_neg {z : ℂ} (hz : z ≠ 0) :
    normalizedArgument (-z) = normalizedArgument z + (1 / 2 : ℝ) := by
  let e : Real.Angle ≃+ UnitAddCircle :=
    AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero
  change e (Complex.arg (-z) : Real.Angle) = e (Complex.arg z) + _
  rw [Complex.arg_neg_coe_angle hz, e.map_add]
  congr 1
  change ((Real.pi * ((2 * Real.pi)⁻¹ * 1) : ℝ) : UnitAddCircle) = _
  congr 1
  field_simp

end CircleDomainRigidity.FiniteTransfer

end

end OAI
