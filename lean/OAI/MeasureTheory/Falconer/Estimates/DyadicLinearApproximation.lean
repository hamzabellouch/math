import OAI.MeasureTheory.Falconer.Estimates.DyadicSecantError

namespace OAI

/-! A finite energy bound gives uniform linear approximation on the whole interval. -/
namespace Falconer
open Set

theorem exists_dyadic_endpoint_near (a : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ)
    {x : ℝ} (hx : x ∈ Icc a (a+h)) :
    ∃ y ∈ dyadicEndpoints a h n, |x-y| ≤ h/(2 : ℝ)^n := by
  induction n generalizing a h with
  | zero =>
    refine ⟨a,by simp [dyadicEndpoints],?_⟩
    rw [pow_zero,div_one,abs_of_nonneg (sub_nonneg.mpr hx.1)]
    linarith [hx.2]
  | succ n ih =>
    by_cases hm : x ≤ a+h/2
    · obtain ⟨y,hy,hxy⟩ := ih a (h := h/2) (div_nonneg hh (by norm_num)) ⟨hx.1,hm⟩
      refine ⟨y,Or.inl hy,hxy.trans_eq ?_⟩
      simp only [div_div,pow_succ,mul_comm]
    · obtain ⟨y,hy,hxy⟩ := ih (a+h/2) (h := h/2) (div_nonneg hh (by norm_num))
        ⟨le_of_not_ge hm,by linarith [hx.2]⟩
      refine ⟨y,Or.inr hy,hxy.trans_eq ?_⟩
      simp only [div_div,pow_succ,mul_comm]

theorem intervalSecantError_abs_sub_le {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    (a : ℝ) {h : ℝ} (hh : 0 < h) (x y : ℝ) :
    |intervalSecantError f a h x-intervalSecantError f a h y| ≤ 4*|x-y| := by
  have hfxy : |f x-f y| ≤ 2*|x-y| := by
    simpa only [Real.dist_eq,NNReal.coe_ofNat] using hf.dist_le_mul x y
  have hs := intervalSecantSlope_abs_le hf a hh
  have he : intervalSecantError f a h x-intervalSecantError f a h y =
      (f x-f y)-intervalSecantSlope f a h*(x-y) := by
    unfold intervalSecantError
    ring
  rw [he]
  calc
    _ ≤ |f x-f y|+|intervalSecantSlope f a h*(x-y)| := by
      simpa only [sub_eq_add_neg,abs_neg] using
        abs_add_le (f x-f y) (-(intervalSecantSlope f a h*(x-y)))
    _ ≤ 2*|x-y|+2*|x-y| := add_le_add hfxy (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hs (abs_nonneg _))
    _ = _ := by ring

theorem dyadic_linear_approximation {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    (a : ℝ) {h η : ℝ} (hh : 0 < h) (hη : 0 ≤ η) (n : ℕ)
    (hv : dyadicSlopeVariance f a h (intervalSecantSlope f a h) n ≤ η^2)
    {x : ℝ} (hx : x ∈ Icc a (a+h)) :
    |intervalSecantError f a h x| ≤ h*η+4*h/(2 : ℝ)^n := by
  obtain ⟨y,hy,hxy⟩ := exists_dyadic_endpoint_near a hh.le n hx
  have hs := dyadic_secant_error_sq_le f a hh n hy
  have hb := mul_le_mul_of_nonneg_left hv (sq_nonneg h)
  have hyerr : |intervalSecantError f a h y| ≤ h*η := by
    have hn := mul_nonneg hh.le hη
    nlinarith [sq_abs (intervalSecantError f a h y)]
  calc
    _ = |intervalSecantError f a h y+
        (intervalSecantError f a h x-intervalSecantError f a h y)| := by congr 1; ring
    _ ≤ |intervalSecantError f a h y|+
        |intervalSecantError f a h x-intervalSecantError f a h y| := abs_add_le _ _
    _ ≤ h*η+4*|x-y| := add_le_add hyerr (intervalSecantError_abs_sub_le hf a hh x y)
    _ ≤ h*η+4*(h/(2 : ℝ)^n) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hxy (by norm_num : (0 : ℝ) ≤ 4))
    _ = _ := by ring

end Falconer

end OAI
