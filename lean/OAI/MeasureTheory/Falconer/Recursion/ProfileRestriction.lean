import OAI.MeasureTheory.Falconer.Estimates.DyadicSecantError

namespace OAI

/-! Quantitative stability when a linear profile interval is shortened on the right. -/
namespace Falconer
open Set

theorem intervalSecantError_restrict_left (f : ℝ → ℝ) (a h x : ℝ)
    {k : ℝ} (hk : k ≠ 0) :
    intervalSecantError f a k x = intervalSecantError f a h x-
      intervalSecantError f a h (a+k)*((x-a)/k) := by
  unfold intervalSecantError
  unfold intervalSecantSlope
  field_simp [hk]
  ring

theorem linear_interval_restrict_left {f : ℝ → ℝ} {a h k ε : ℝ}
    (hk : 0 < k) (hkh : k ≤ h) (hε : 0 ≤ ε)
    (herr : ∀ x ∈ Icc a (a+h), |intervalSecantError f a h x| ≤ ε*h)
    {x : ℝ} (hx : x ∈ Icc a (a+k)) :
    |intervalSecantError f a k x| ≤ 2*ε*h := by
  have hr0 : 0 ≤ (x-a)/k := div_nonneg (sub_nonneg.mpr hx.1) hk.le
  have hr1 : (x-a)/k ≤ 1 := (div_le_iff₀ hk).2 (by linarith [hx.2])
  have hv := herr (a+k) ⟨by linarith,by linarith⟩
  have hx' := herr x ⟨hx.1,by linarith [hx.2]⟩
  rw [intervalSecantError_restrict_left f a h x hk.ne']
  calc
    _ ≤ |intervalSecantError f a h x|+
        |intervalSecantError f a h (a+k)*((x-a)/k)| := by
      simpa only [sub_eq_add_neg,abs_neg] using abs_add_le
        (intervalSecantError f a h x) (-(intervalSecantError f a h (a+k)*((x-a)/k)))
    _ = |intervalSecantError f a h x|+
        |intervalSecantError f a h (a+k)| *((x-a)/k) := by
      rw [abs_mul,abs_of_nonneg hr0]
    _ ≤ ε*h+ε*h := add_le_add hx' ((mul_le_mul_of_nonneg_right hv hr0).trans
      (mul_le_of_le_one_right (mul_nonneg hε (hk.le.trans hkh)) hr1))
    _ = _ := by ring

theorem linear_interval_restrict_proportion {f : ℝ → ℝ} {a h k η : ℝ}
    (hk : 0 < k) (hkh : k ≤ h) (hη : 0 < η) (hsize : η*h ≤ k)
    (herr : ∀ x ∈ Icc a (a+h), |intervalSecantError f a h x| ≤ η^2*h)
    {x : ℝ} (hx : x ∈ Icc a (a+k)) :
    |intervalSecantError f a k x| ≤ 2*η*k := by
  have he := linear_interval_restrict_left hk hkh (sq_nonneg η) herr hx
  have hb := mul_le_mul_of_nonneg_left hsize (show 0 ≤ 2*η by positivity)
  nlinarith

end Falconer

end OAI
