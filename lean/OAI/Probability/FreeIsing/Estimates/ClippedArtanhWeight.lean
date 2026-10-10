import Mathlib

namespace OAI

noncomputable section
open MeasureTheory
open scoped NNReal

namespace Problem367.ClippedArtanhWeight

def clip (r x : ℝ) : ℝ := max (-r) (min r x)

def weight (r x : ℝ) : ℝ := 1 / (1 - clip r x ^ 2)

theorem continuous_clip (r : ℝ) : Continuous (clip r) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem abs_clip_le {r : ℝ} (hr : 0 ≤ r) (x : ℝ) : |clip r x| ≤ r := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem clip_eq_of_abs_le {r x : ℝ} (hx : |x| ≤ r) : clip r x = x := by
  have h := abs_le.mp hx
  simp only [clip, min_eq_right h.2, max_eq_right h.1]

theorem denominator_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    0 < 1 - clip r x ^ 2 := by
  have hs : clip r x ^ 2 ≤ r ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (clip r x)) hr0).mpr (abs_clip_le hr0 x)
  nlinarith

theorem weight_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    0 < weight r x :=
  div_pos zero_lt_one (denominator_pos hr0 hr1 x)

theorem abs_weight_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    |weight r x| ≤ 1 / (1 - r ^ 2) := by
  rw [abs_of_pos (weight_pos hr0 hr1 x)]
  have hs : clip r x ^ 2 ≤ r ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (clip r x)) hr0).mpr (abs_clip_le hr0 x)
  exact one_div_le_one_div_of_le (by nlinarith) (by linarith)

theorem continuous_weight {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (weight r) :=
  continuous_const.div (continuous_const.sub ((continuous_clip r).pow 2))
    (fun x => (denominator_pos hr0 hr1 x).ne')

theorem weight_eq_of_abs_le {r x : ℝ} (hx : |x| ≤ r) :
    weight r x = 1 / (1 - x ^ 2) := by
  rw [weight, clip_eq_of_abs_le hx]

theorem weight_mul_covariance_eq {r m C R : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hm : |m| ≤ r)
    (hC : C = (1 - m ^ 2) * R) : weight r m * C = R := by
  have hd : 1 - m ^ 2 ≠ 0 := by
    simpa only [clip_eq_of_abs_le hm] using (denominator_pos hr0 hr1 m).ne'
  rw [weight_eq_of_abs_le hm, hC]
  field_simp

theorem progressive_weight {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : IsStronglyProgressive F M) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    IsStronglyProgressive F (fun t ω => weight r (M t ω)) :=
  fun t => (continuous_weight hr0 hr1).comp_stronglyMeasurable (hM t)

theorem continuous_weight_comp_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {M : ℝ≥0 → Ω → ℝ}
    (hM : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∀ᵐ ω ∂P, Continuous (fun t => weight r (M t ω)) :=
  hM.mono (fun _ h => (continuous_weight hr0 hr1).comp h)

end Problem367.ClippedArtanhWeight

end

end OAI
