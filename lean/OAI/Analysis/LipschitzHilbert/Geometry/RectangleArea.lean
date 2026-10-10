import OAI.Analysis.LipschitzHilbert.Estimates.PlaneCoordinates
import Mathlib.MeasureTheory.Group.Measure

namespace OAI

/-! Exact area of the orthogonal rectangles in the published input. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.Rectangle

def orthogonalCoordinates (R : Rectangle) : Plane ≃ᵐ (ℝ × ℝ) :=
  (MeasurableEquiv.subRight R.center).trans
    (R.axes.measurableEquiv.trans planeCoordinates.symm)

theorem orthogonalCoordinates_apply (R : Rectangle) (z : Plane) :
    R.orthogonalCoordinates z = (R.axes.repr (z-R.center) 0, R.axes.repr (z-R.center) 1) := rfl

theorem orthogonalCoordinates_measurePreserving (R : Rectangle) :
    MeasurePreserving R.orthogonalCoordinates volume (volume.prod volume) := by
  exact planeCoordinates_measurePreserving.symm.comp
    (R.axes.measurePreserving_repr.comp (measurePreserving_sub_right volume R.center))

theorem carrier_eq_coordinate_rectangle (R : Rectangle) :
    R.carrier = R.orthogonalCoordinates ⁻¹'
      (Icc (-R.long/2) (R.long/2) ×ˢ Icc (-R.short/2) (R.short/2)) := by
  ext z
  simp only [carrier, mem_ofPred_eq, mem_preimage, mem_prod, mem_Icc,
    orthogonalCoordinates_apply, abs_le, neg_div]

theorem volume_carrier (R : Rectangle) :
    volume R.carrier = ENNReal.ofReal R.long * ENNReal.ofReal R.short := by
  rw [carrier_eq_coordinate_rectangle,
    R.orthogonalCoordinates_measurePreserving.measure_preimage_equiv,
    Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
  congr 2 <;> ring

theorem volume_carrier_ne_top (R : Rectangle) : volume R.carrier ≠ ∞ := by
  rw [volume_carrier]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

theorem volume_carrier_pos (R : Rectangle) : 0 < volume R.carrier := by
  rw [volume_carrier]
  have hl := lt_of_lt_of_le R.short_pos R.short_le_long
  exact bot_lt_iff_ne_bot.mpr (mul_ne_zero
    (ne_of_gt (ENNReal.ofReal_pos.mpr hl))
    (ne_of_gt (ENNReal.ofReal_pos.mpr R.short_pos)))

end LipschitzHilbert.Rectangle

end

end OAI
