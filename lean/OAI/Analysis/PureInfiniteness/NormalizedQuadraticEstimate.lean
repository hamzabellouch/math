import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

namespace OAI

/-! Quantitative normalization for finite tracial vector approximations. -/

noncomputable section
open scoped InnerProductSpace

namespace WeakPureInfiniteness

lemma normalized_scalar_error {s α q δ : ℝ} (hs : 1 / 2 < s)
    (hm : |1 - s| < δ) (hq : |α - q| < δ) :
    |α - s⁻¹ * q| < 2 * δ * (1 + |α|) := by
  have hs0 : 0 < s := by linarith
  have hi : s⁻¹ ≤ 2 := (inv_le_comm₀ hs0 (by norm_num)).mpr (by linarith)
  have he : α - s⁻¹ * q = s⁻¹ * ((α - q) + (s - 1) * α) := by
    field_simp [hs0.ne']
    ring
  rw [he, abs_mul, abs_of_pos (inv_pos.mpr hs0)]
  have hm' : |s - 1| < δ := by simpa only [abs_sub_comm] using hm
  calc
    s⁻¹ * |(α - q) + (s - 1) * α| ≤
        s⁻¹ * (|α - q| + |s - 1| * |α|) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hs0.le)
      exact (abs_add_le _ _).trans (by rw [abs_mul])
    _ < s⁻¹ * (δ + δ * |α|) := by
      apply mul_lt_mul_of_pos_left _ (inv_pos.mpr hs0)
      exact add_lt_add_of_lt_of_le hq (mul_le_mul_of_nonneg_right hm'.le (abs_nonneg _))
    _ ≤ 2 * (δ + δ * |α|) := by
      apply mul_le_mul_of_nonneg_right hi
      have hd : 0 < δ := (abs_nonneg _).trans_lt hq
      positivity
    _ = 2 * δ * (1 + |α|) := by ring

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma inner_normalized_real (r : H) (T : H →L[ℂ] H) :
    (inner ℂ (((‖r‖⁻¹ : ℝ) : ℂ) • r) (T (((‖r‖⁻¹ : ℝ) : ℂ) • r))).re =
      (‖r‖ ^ 2)⁻¹ * (inner ℂ r (T r)).re := by
  rw [map_smul, inner_smul_left, inner_smul_right]
  rw [starRingEnd_apply, Complex.star_def, Complex.conj_ofReal,
    ← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  have hc : ‖r‖⁻¹ * ‖r‖⁻¹ = (‖r‖ ^ 2)⁻¹ := by
    rw [← pow_two, inv_pow]
  rw [hc]

lemma normalized_quadratic_error (r : H) (T : H →L[ℂ] H) {α δ : ℝ}
    (hs : 1 / 2 < ‖r‖ ^ 2) (hm : |1 - ‖r‖ ^ 2| < δ)
    (hq : |α - (inner ℂ r (T r)).re| < δ) :
    |α - (inner ℂ (((‖r‖⁻¹ : ℝ) : ℂ) • r) (T (((‖r‖⁻¹ : ℝ) : ℂ) • r))).re| <
      2 * δ * (1 + |α|) := by
  rw [inner_normalized_real]
  exact normalized_scalar_error hs hm hq

end WeakPureInfiniteness

end

end OAI
