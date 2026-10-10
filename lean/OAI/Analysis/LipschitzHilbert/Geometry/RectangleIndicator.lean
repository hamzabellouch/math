import OAI.Analysis.LipschitzHilbert.Geometry.RectangleArea
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

namespace OAI

/-! Indicator tests in the precise normalization of the published
rectangle maximal estimate. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert

theorem squareIntegral_indicator (Q : Set Plane) (hQ : MeasurableSet Q) :
    squareIntegral volume (Q.indicator (fun _ => (1:ℝ))) = volume Q := by
  unfold squareIntegral
  have heq (x : Plane) : ‖Q.indicator (fun _ => (1:ℝ)) x‖ₑ^2 =
      Q.indicator (fun _ => (1:ℝ≥0∞)) x := by
    by_cases hx : x ∈ Q <;> simp [hx]
  simp_rw [heq]
  exact lintegral_indicator_fun_one hQ

namespace Rectangle

theorem average_indicator (R : Rectangle) (Q : Set Plane) (hQ : MeasurableSet Q) :
    R.average (Q.indicator (fun _ => (1:ℝ))) =
      (volume R.carrier)⁻¹ * volume (R.carrier ∩ Q) := by
  unfold average
  have heq (x : Plane) : ‖Q.indicator (fun _ => (1:ℝ)) x‖ₑ =
      Q.indicator (fun _ => (1:ℝ≥0∞)) x := by
    by_cases hx : x ∈ Q <;> simp [hx]
  simp_rw [heq]
  rw [lintegral_indicator_fun_one hQ, Measure.restrict_apply hQ, inter_comm]

theorem indicator_average_lower (R : Rectangle) (Q S : Set Plane) (hQ : MeasurableSet Q)
    (hsub : S ⊆ Q ∩ R.carrier) (B β : ℝ) (_hB : 0 < B) (hβ : 0 ≤ β)
    (harea : volume R.carrier ≤ ENNReal.ofReal B)
    (hintersection : ENNReal.ofReal (β*B) ≤ volume S) :
    ENNReal.ofReal β ≤ R.average (Q.indicator (fun _ => (1:ℝ))) := by
  rw [average_indicator R Q hQ]
  have hnum : ENNReal.ofReal β * volume R.carrier ≤ volume (R.carrier ∩ Q) := by
    calc
      _ ≤ ENNReal.ofReal β*ENNReal.ofReal B := mul_le_mul' le_rfl harea
      _ = ENNReal.ofReal (β*B) := (ENNReal.ofReal_mul hβ).symm
      _ ≤ volume S := hintersection
      _ ≤ _ := measure_mono (by simpa only [inter_comm] using hsub)
  have h := mul_le_mul' (le_refl ((volume R.carrier)⁻¹)) hnum
  simpa only [← mul_assoc, mul_left_comm ((volume R.carrier)⁻¹) (ENNReal.ofReal β),
    ENNReal.inv_mul_cancel R.volume_carrier_pos.ne' R.volume_carrier_ne_top, mul_one] using h

theorem average_indicator_ge_measure_div (R : Rectangle) (Q S : Set Plane)
    (hQ : MeasurableSet Q) (hsub : S ⊆ Q ∩ R.carrier) (B : ℝ≥0∞)
    (harea : volume R.carrier ≤ B) :
    volume S / B ≤ R.average (Q.indicator (fun _ => (1:ℝ))) := by
  rw [average_indicator R Q hQ, div_eq_mul_inv, mul_comm (volume S)]
  exact mul_le_mul' (ENNReal.inv_le_inv.mpr harea)
    (measure_mono (by simpa only [inter_comm] using hsub))

end Rectangle
end LipschitzHilbert

end

end OAI
