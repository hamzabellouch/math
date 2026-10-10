import OAI.MeasureTheory.Falconer.Estimates.DyadicSlopeVariance

namespace OAI

/-! Pointwise straight-line error on the dyadic vertices is controlled by
the centered slope energy, without any differentiability assumption. -/
namespace Falconer
open Set

noncomputable def intervalSecantError (f : ℝ → ℝ) (a h x : ℝ) : ℝ :=
  f x-f a-intervalSecantSlope f a h*(x-a)

def dyadicEndpoints (a h : ℝ) : ℕ → Set ℝ
  | 0 => {a,a+h}
  | n+1 => dyadicEndpoints a (h/2) n ∪ dyadicEndpoints (a+h/2) (h/2) n

theorem dyadicEndpoints_bounds (a : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ)
    {x : ℝ} (hx : x ∈ dyadicEndpoints a h n) : a ≤ x ∧ x ≤ a+h := by
  induction n generalizing a h with
  | zero =>
    simp only [dyadicEndpoints,mem_insert_iff,mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> constructor <;> linarith
  | succ n ih =>
    rcases hx with hx | hx
    · have hb := ih a (div_nonneg hh (by norm_num)) hx
      constructor <;> linarith
    · have hb := ih (a+h/2) (div_nonneg hh (by norm_num)) hx
      constructor <;> linarith

theorem intervalSecantError_left (f : ℝ → ℝ) (a h x : ℝ) :
    intervalSecantError f a h x = intervalSecantError f a (h/2) x+
      (intervalSecantSlope f a (h/2)-intervalSecantSlope f a h)*(x-a) := by
  unfold intervalSecantError
  ring

theorem intervalSecantError_right (f : ℝ → ℝ) (a x : ℝ) {h : ℝ} (hh : h ≠ 0) :
    intervalSecantError f a h x = intervalSecantError f (a+h/2) (h/2) x+
      (intervalSecantSlope f (a+h/2) (h/2)-intervalSecantSlope f a h)*(x-a-h) := by
  unfold intervalSecantError intervalSecantSlope
  rw [show a+h/2+h/2 = a+h by ring]
  field_simp [hh]
  ring

private theorem secant_error_algebra {e d t h v V : ℝ}
    (he : e^2 ≤ (h/2)^2*v) (ht : t^2 ≤ (h/2)^2)
    (hv : (v+d^2)/2 ≤ V) : (e+d*t)^2 ≤ h^2*V := by
  have hd := mul_le_mul_of_nonneg_left ht (sq_nonneg d)
  have hV := mul_le_mul_of_nonneg_left hv (sq_nonneg h)
  nlinarith [sq_nonneg (e-d*t)]

theorem dyadic_secant_error_sq_le (f : ℝ → ℝ) (a : ℝ) {h : ℝ} (hh : 0 < h)
    (n : ℕ) {x : ℝ} (hx : x ∈ dyadicEndpoints a h n) :
    (intervalSecantError f a h x)^2 ≤
      h^2*dyadicSlopeVariance f a h (intervalSecantSlope f a h) n := by
  induction n generalizing a h with
  | zero =>
    have he : intervalSecantError f a h x = 0 := by
      simp only [dyadicEndpoints,mem_insert_iff,mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · simp [intervalSecantError]
      · unfold intervalSecantError intervalSecantSlope
        field_simp [hh.ne']
        ring
    rw [he]
    simpa only [zero_pow (by decide : 2 ≠ 0)] using
      mul_nonneg (sq_nonneg h) (dyadicSlopeVariance_nonneg f a h (intervalSecantSlope f a h) 0)
  | succ n ih =>
    have hvar := dyadicSlopeVariance_child_le f a hh n
    rcases hx with hx | hx
    · have he := ih a (half_pos hh) hx
      have hb := dyadicEndpoints_bounds a (div_nonneg hh.le (by norm_num)) n hx
      rw [intervalSecantError_left]
      apply secant_error_algebra he ?_ hvar.1
      nlinarith [sq_nonneg (x-a)]
    · have he := ih (a+h/2) (half_pos hh) hx
      have hb := dyadicEndpoints_bounds (a+h/2) (div_nonneg hh.le (by norm_num)) n hx
      rw [intervalSecantError_right f a x hh.ne']
      apply secant_error_algebra he ?_ hvar.2
      nlinarith [sq_nonneg (x-a-h)]

end Falconer

end OAI
