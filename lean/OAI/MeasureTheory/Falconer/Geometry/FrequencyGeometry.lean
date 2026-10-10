import OAI.MeasureTheory.Falconer.Angular.AngularTubeMean

namespace OAI

/-! # Frequency-ball preimages under the radial map -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scaled_unit_difference {w u : E} (hw : ‖w‖ = 1) (hu : ‖u‖ = 1)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a*‖w-u‖ ≤ 2*‖a • w-b • u‖ := by
  have hab : |a-b| ≤ ‖a • w-b • u‖ := by
    have h := abs_norm_sub_norm_le (a • w) (b • u)
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb,hw,hu,mul_one] using h
  have he : a • (w-u) = (a • w-b • u)+(b-a) • u := by module
  have h := norm_add_le (a • w-b • u) ((b-a) • u)
  rw [← he,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg ha,hu,mul_one,
    abs_sub_comm b a] at h
  linarith

theorem radial_direction_close {w : E} (hw : ‖w‖ = 1) {v : E}
    (hv : v ≠ 0) {t r B : ℝ} (hB : 0 < B) (ht : B ≤ |t|)
    (hr : ‖t • w-v‖ < r) :
    ‖w-‖v‖⁻¹ • v‖ < 2*r/B ∨ ‖w-(-‖v‖⁻¹ • v)‖ < 2*r/B := by
  have hvp := norm_pos_iff.mpr hv
  let u := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by
    simp only [u,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hvp),inv_mul_cancel₀ hvp.ne']
  have hvu : ‖v‖ • u = v := by simp [u,smul_smul,hvp.ne']
  rcases le_total 0 t with ht₀ | ht₀
  · left
    have h := scaled_unit_difference hw hu ht₀ (norm_nonneg v)
    rw [hvu] at h
    rw [abs_of_nonneg ht₀] at ht
    apply (lt_div_iff₀ hB).mpr
    have hn := norm_nonneg (w-u)
    nlinarith
  · right
    rw [neg_smul]
    change ‖w-(-u)‖ < 2*r/B
    have h := scaled_unit_difference (show ‖-w‖ = 1 by simpa only [norm_neg] using hw)
      hu (neg_nonneg.mpr ht₀) (norm_nonneg v)
    rw [hvu,neg_smul,smul_neg,neg_neg] at h
    have he : ‖-w-u‖ = ‖w-(-u)‖ := by
      rw [show -w-u = -(w-(-u)) by abel,norm_neg]
    rw [he] at h
    rw [abs_of_nonpos ht₀] at ht
    apply (lt_div_iff₀ hB).mpr
    have hn := norm_nonneg (w-(-u))
    nlinarith

theorem radial_norm_interval {w v : E} (hw : ‖w‖ = 1) {t r : ℝ}
    (hr : ‖t • w-v‖ < r) : |t| ∈ Ioo (‖v‖-r) (‖v‖+r) := by
  have h := (abs_norm_sub_norm_le (t • w) v).trans_lt hr
  simp only [norm_smul,Real.norm_eq_abs,hw,mul_one] at h
  rw [abs_lt] at h
  constructor <;> linarith [h.1,h.2]

end Falconer

end OAI
