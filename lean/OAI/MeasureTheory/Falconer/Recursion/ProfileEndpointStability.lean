import OAI.MeasureTheory.Falconer.Estimates.DyadicLinearApproximation

namespace OAI

/-! Endpoint stability for moving the selected profile intervals onto the
actual integer block grid. -/
namespace Falconer
open Set

theorem intervalSecantError_change_interval (f : ℝ → ℝ) (a h u x : ℝ)
    {k : ℝ} (hk : k ≠ 0) :
    intervalSecantError f u k x-intervalSecantError f a h x =
      -((1-(x-u)/k)*intervalSecantError f a h u+
        ((x-u)/k)*intervalSecantError f a h (u+k)) := by
  unfold intervalSecantError intervalSecantSlope
  field_simp [hk]
  ring

theorem intervalSecantError_change_bound (f : ℝ → ℝ) (a h u : ℝ)
    {k A : ℝ} (hk : 0 < k)
    (hleft : |intervalSecantError f a h u| ≤ A)
    (hright : |intervalSecantError f a h (u+k)| ≤ A)
    {x : ℝ} (hx : x ∈ Icc u (u+k)) :
    |intervalSecantError f u k x-intervalSecantError f a h x| ≤ A := by
  have ht0 : 0 ≤ (x-u)/k := div_nonneg (sub_nonneg.mpr hx.1) hk.le
  have ht1 : (x-u)/k ≤ 1 := (div_le_iff₀ hk).2 (by linarith [hx.2])
  have hs0 : 0 ≤ 1-(x-u)/k := sub_nonneg.mpr ht1
  rw [intervalSecantError_change_interval f a h u x hk.ne',abs_neg]
  calc
    _ ≤ |(1-(x-u)/k)*intervalSecantError f a h u|+
        |((x-u)/k)*intervalSecantError f a h (u+k)| := abs_add_le _ _
    _ = (1-(x-u)/k)*|intervalSecantError f a h u|+
        ((x-u)/k)*|intervalSecantError f a h (u+k)| := by
      rw [abs_mul,abs_mul,abs_of_nonneg hs0,abs_of_nonneg ht0]
    _ ≤ (1-(x-u)/k)*A+((x-u)/k)*A := add_le_add
      (mul_le_mul_of_nonneg_left hleft hs0) (mul_le_mul_of_nonneg_left hright ht0)
    _ = A := by ring

theorem intervalSecantError_at_end (f : ℝ → ℝ) (a : ℝ) {h : ℝ} (hh : h ≠ 0) :
    intervalSecantError f a h (a+h) = 0 := by
  unfold intervalSecantError intervalSecantSlope
  field_simp [hh]
  ring

theorem intervalSecantError_near_endpoints {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    (a : ℝ) {h u k ρ : ℝ} (hh : 0 < h)
    (hu : |u-a| ≤ ρ) (hv : |u+k-(a+h)| ≤ ρ) :
    |intervalSecantError f a h u| ≤ 4*ρ ∧
      |intervalSecantError f a h (u+k)| ≤ 4*ρ := by
  have hleft := intervalSecantError_abs_sub_le hf a hh u a
  have hright := intervalSecantError_abs_sub_le hf a hh (u+k) (a+h)
  have ha : intervalSecantError f a h a = 0 := by simp [intervalSecantError]
  rw [ha,sub_zero] at hleft
  rw [intervalSecantError_at_end f a hh.ne',sub_zero] at hright
  constructor
  · exact hleft.trans (mul_le_mul_of_nonneg_left hu (by norm_num))
  · exact hright.trans (mul_le_mul_of_nonneg_left hv (by norm_num))

theorem intervalSecantError_grid_stability {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    (a : ℝ) {h u k ρ : ℝ} (hh : 0 < h) (hk : 0 < k)
    (hu : |u-a| ≤ ρ) (hv : |u+k-(a+h)| ≤ ρ)
    {x : ℝ} (hx : x ∈ Icc u (u+k)) :
    |intervalSecantError f u k x-intervalSecantError f a h x| ≤ 4*ρ := by
  have he := intervalSecantError_near_endpoints hf a hh hu hv
  exact intervalSecantError_change_bound f a h u hk he.1 he.2 hx

theorem intervalSecantSlope_change_interval (f : ℝ → ℝ) (a h u : ℝ)
    {k : ℝ} (hk : k ≠ 0) :
    intervalSecantSlope f u k-intervalSecantSlope f a h =
      (intervalSecantError f a h (u+k)-intervalSecantError f a h u)/k := by
  unfold intervalSecantError intervalSecantSlope
  field_simp [hk]
  ring

theorem intervalSecantSlope_change_bound (f : ℝ → ℝ) (a h u : ℝ)
    {k A : ℝ} (hk : 0 < k)
    (hleft : |intervalSecantError f a h u| ≤ A)
    (hright : |intervalSecantError f a h (u+k)| ≤ A) :
    |intervalSecantSlope f u k-intervalSecantSlope f a h| ≤ 2*A/k := by
  rw [intervalSecantSlope_change_interval f a h u hk.ne',abs_div,abs_of_pos hk]
  apply div_le_div_of_nonneg_right _ hk.le
  have he : |intervalSecantError f a h (u+k)-intervalSecantError f a h u| ≤
      |intervalSecantError f a h (u+k)|+|intervalSecantError f a h u| := by
    simpa only [sub_eq_add_neg,abs_neg] using
      abs_add_le (intervalSecantError f a h (u+k)) (-intervalSecantError f a h u)
  linarith

theorem intervalSecantSlope_grid_stability {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    (a : ℝ) {h u k ρ : ℝ} (hh : 0 < h) (hk : 0 < k)
    (hu : |u-a| ≤ ρ) (hv : |u+k-(a+h)| ≤ ρ) :
    |intervalSecantSlope f u k-intervalSecantSlope f a h| ≤ 8*ρ/k := by
  have he := intervalSecantError_near_endpoints hf a hh hu hv
  convert intervalSecantSlope_change_bound f a h u hk he.1 he.2 using 1; ring

end Falconer

end OAI
