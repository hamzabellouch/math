import OAI.NumberTheory.TwoPoint.Fourier.ModFiveContourKernel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace OAI

/-! A short multiplicative smoothing of Perron's kernel. The difference
has both the first-order bound and an integrable inverse-square tail. -/

namespace TwoPointCorrelations

open Complex

noncomputable def halaszPerronWindowKernel (x δ : ℝ) (s : ℂ) : ℂ :=
  (((1 + δ : ℝ) : ℂ) * modFivePerronKernel ((1 + δ) * x) s -
    modFivePerronKernel x s) / (δ : ℂ)

lemma halasz_exp_window_difference {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (t : ℝ) :
    ‖Complex.exp (((2 : ℂ) + (t : ℂ) * Complex.I) * (Real.log (1 + δ) : ℂ)) - 1‖ ≤
      δ * (3 + |t|) := by
  have hy : 0 < 1 + δ := by linarith
  have hlog0 : 0 ≤ Real.log (1 + δ) := Real.log_nonneg (by linarith)
  have hlog : Real.log (1 + δ) ≤ δ := by
    simpa only [add_sub_cancel_left] using Real.log_le_sub_one_of_pos hy
  let z := Complex.exp (((t * Real.log (1 + δ) : ℝ) : ℂ) * Complex.I)
  have hz : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hz1 : ‖z - 1‖ ≤ |t| * Real.log (1 + δ) := by
    have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * Real.log (1 + δ))
    simpa only [z, mul_comm Complex.I, Real.norm_eq_abs, abs_mul, abs_of_nonneg hlog0] using h
  have he : Complex.exp (((2 : ℂ) + (t : ℂ) * Complex.I) *
      (Real.log (1 + δ) : ℂ)) = (((1 + δ) ^ 2 : ℝ) : ℂ) * z := by
    rw [show ((2 : ℂ) + (t : ℂ) * Complex.I) * (Real.log (1 + δ) : ℂ) =
      ((2 * Real.log (1 + δ) : ℝ) : ℂ) +
        (((t * Real.log (1 + δ) : ℝ) : ℂ) * Complex.I) by push_cast; ring,
      Complex.exp_add, ← Complex.ofReal_exp]
    congr 1
    exact_mod_cast (show Real.exp (2 * Real.log (1 + δ)) = (1 + δ) ^ 2 by
      simpa only [Nat.cast_ofNat, Real.exp_log hy] using Real.exp_nat_mul (Real.log (1 + δ)) 2)
  rw [he, show (((1 + δ) ^ 2 : ℝ) : ℂ) * z - 1 =
    (((1 + δ) ^ 2 - 1 : ℝ) : ℂ) * z + (z - 1) by push_cast; ring]
  calc
    _ ≤ ‖(((1 + δ) ^ 2 - 1 : ℝ) : ℂ) * z‖ + ‖z - 1‖ := norm_add_le _ _
    _ ≤ ((1 + δ) ^ 2 - 1) + |t| * Real.log (1 + δ) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hz, mul_one,
        abs_of_nonneg (by nlinarith : 0 ≤ (1 + δ) ^ 2 - 1)]
      exact add_le_add le_rfl hz1
    _ ≤ δ * (3 + |t|) := by
      have hm := mul_le_mul_of_nonneg_left hlog (abs_nonneg t)
      nlinarith

lemma halasz_perron_window_factor {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) (s : ℂ) :
    halaszPerronWindowKernel x δ s =
      (x : ℂ) ^ s * (Complex.exp ((s + 1) * (Real.log (1 + δ) : ℂ)) - 1) /
        ((δ : ℂ) * s * (s + 1)) := by
  have hy : 0 < 1 + δ := by linarith
  have hyexp : ((1 + δ : ℝ) : ℂ) * ((1 + δ : ℝ) : ℂ) ^ s =
      Complex.exp ((s + 1) * (Real.log (1 + δ) : ℂ)) := by
    calc
      _ = ((1 + δ : ℝ) : ℂ) ^ (s + 1) := by
        rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy.ne'), Complex.cpow_one]
        ring
      _ = _ := by
        rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
          ← Complex.ofReal_log hy.le]
        congr 1
        ring
  unfold halaszPerronWindowKernel modFivePerronKernel
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hy.le hx.le]
  calc
    _ = (x : ℂ) ^ s *
        (((1 + δ : ℝ) : ℂ) * ((1 + δ : ℝ) : ℂ) ^ s - 1) /
          ((δ : ℂ) * s * (s + 1)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [hyexp]

theorem halasz_perron_window_bound {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (t : ℝ) :
    ‖halaszPerronWindowKernel x δ (1 + (t : ℂ) * Complex.I)‖ ≤
      4 * x / ‖1 + (t : ℂ) * Complex.I‖ := by
  let s : ℂ := 1 + (t : ℂ) * Complex.I
  have hs : 1 ≤ ‖s‖ := by simpa [s] using Complex.abs_re_le_norm s
  have hs1 : 2 ≤ ‖s + 1‖ := by
    have h := Complex.abs_re_le_norm (s + 1)
    norm_num [s] at h
    exact h
  have ht : |t| ≤ ‖s + 1‖ := by simpa [s] using Complex.abs_im_le_norm (s + 1)
  have hs0 : 0 < ‖s‖ := by linarith
  have hs10 : 0 < ‖s + 1‖ := by linarith
  have he : ‖Complex.exp ((s + 1) * (Real.log (1 + δ) : ℂ)) - 1‖ ≤
      δ * (4 * ‖s + 1‖) := by
    have he := halasz_exp_window_difference hδ hδ1 t
    have hshape : s + 1 = (2 : ℂ) + (t : ℂ) * Complex.I := by dsimp [s]; ring
    rw [hshape]
    apply he.trans
    have hnorm : 3 + |t| ≤ 4 * ‖s + 1‖ := by linarith
    rw [← hshape]
    exact mul_le_mul_of_nonneg_left hnorm hδ.le
  rw [halasz_perron_window_factor hx hδ, norm_div, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  change x ^ s.re * ‖Complex.exp ((s + 1) * (Real.log (1 + δ) : ℂ)) - 1‖ /
    ‖(δ : ℂ) * s * (s + 1)‖ ≤ 4 * x / ‖s‖
  have hre : s.re = 1 := by simp [s]
  rw [hre, Real.rpow_one, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hδ]
  calc
    _ ≤ x * (δ * (4 * ‖s + 1‖)) / (δ * ‖s‖ * ‖s + 1‖) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he hx.le) (by positivity)
    _ = _ := by field_simp [ne_of_gt hδ, ne_of_gt hs0, ne_of_gt hs10]

theorem halasz_perron_window_tail {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (t : ℝ) :
    ‖halaszPerronWindowKernel x δ (1 + (t : ℂ) * Complex.I)‖ ≤
      20 * x / (δ * (1 + t ^ 2)) := by
  have hy : 0 < 1 + δ := by linarith
  have hk1 := modFive_perron_kernel_vertical (mul_pos hy hx) (by norm_num : (1 / 2 : ℝ) ≤ 1) t
  have hk0 := modFive_perron_kernel_vertical hx (by norm_num : (1 / 2 : ℝ) ≤ 1) t
  simp only [Real.rpow_one] at hk1 hk0
  unfold halaszPerronWindowKernel
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  apply (div_le_div_of_nonneg_right (norm_sub_le _ _) hδ.le).trans
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
  have htop : (1 + δ) * ‖modFivePerronKernel ((1 + δ) * x)
      (1 + (t : ℂ) * Complex.I)‖ + ‖modFivePerronKernel x (1 + (t : ℂ) * Complex.I)‖ ≤
      20 * x / (1 + t ^ 2) := by
    calc
      _ ≤ (1 + δ) * (4 * ((1 + δ) * x) / (1 + t ^ 2)) + 4 * x / (1 + t ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hk1 hy.le) hk0
      _ ≤ _ := by
        have hδ2 : (1 + δ) ^ 2 ≤ 4 := by nlinarith
        have hnum : (1 + δ) * (4 * ((1 + δ) * x)) + 4 * x ≤ 20 * x := by
          nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hδ2)]
        calc
          _ = ((1 + δ) * (4 * ((1 + δ) * x)) + 4 * x) / (1 + t ^ 2) := by ring
          _ ≤ _ := div_le_div_of_nonneg_right hnum (by positivity)
  exact (div_le_div_of_nonneg_right htop hδ.le).trans_eq (by
    field_simp [ne_of_gt hδ, show (1 + t ^ 2 : ℝ) ≠ 0 by positivity])

end TwoPointCorrelations

end OAI
