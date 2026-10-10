import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowKernelDerivative

namespace OAI

/-! # An integrable majorant uniform in the spatial parameter -/

open MeasureTheory

namespace DefocusingNLS

theorem one_add_div_rpow_le (c a u : ℝ) (hc : 0 < c) (ha : 0 ≤ a) (hu : 0 ≤ u) :
    (1 + u / c) ^ a ≤ (1 + c⁻¹) ^ a * (1 + u ^ a) := by
  by_cases h : u ≤ 1
  · have hb : 1 + u / c ≤ 1 + c⁻¹ := by rw [← one_div]; gcongr
    calc
      (1 + u / c) ^ a ≤ (1 + c⁻¹) ^ a := Real.rpow_le_rpow (by positivity) hb ha
      _ ≤ (1 + c⁻¹) ^ a * (1 + u ^ a) := by
        nlinarith [Real.rpow_nonneg (by positivity : 0 ≤ 1 + c⁻¹) a,
          Real.rpow_nonneg hu a]
  · have hu1 : 1 ≤ u := le_of_not_ge h
    have hb : 1 + u / c ≤ (1 + c⁻¹) * u := by
      rw [div_eq_mul_inv]
      nlinarith
    calc
      (1 + u / c) ^ a ≤ ((1 + c⁻¹) * u) ^ a :=
        Real.rpow_le_rpow (by positivity) hb ha
      _ = (1 + c⁻¹) ^ a * u ^ a := Real.mul_rpow (by positivity) hu
      _ ≤ (1 + c⁻¹) ^ a * (1 + u ^ a) := by gcongr; linarith

theorem one_add_real_div_bounds_of_re (x : ℂ) (c : ℝ) (hc : 0 < c)
    (hx : c ≤ x.re) {u : ℝ} (hu : 0 ≤ u) :
    1 ≤ ‖1 + (u : ℂ) / x‖ ∧ ‖1 + (u : ℂ) / x‖ ≤ 1 + u / c := by
  have hxc : c ≤ ‖x‖ := hx.trans (Complex.re_le_norm x)
  have hxpos : 0 < ‖x‖ := hc.trans_le hxc
  constructor
  · apply le_trans (b := (1 + (u : ℂ) / x).re) _ (Complex.re_le_norm _)
    simp only [Complex.add_re, Complex.one_re, Complex.div_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, zero_div, add_zero]
    have : 0 ≤ u * x.re / Complex.normSq x :=
      div_nonneg (mul_nonneg hu (hc.le.trans hx)) (Complex.normSq_nonneg x)
    linarith
  · calc
      ‖1 + (u : ℂ) / x‖ ≤ 1 + u / ‖x‖ := by
        simpa only [norm_one, norm_div, Complex.norm_of_nonneg hu] using
          norm_add_le (1 : ℂ) ((u : ℂ) / x)
      _ ≤ 1 + u / c := by gcongr

theorem integrable_exp_neg_mul_rpow (s : ℝ) (hs : -1 < s) :
    IntegrableOn (fun u : ℝ => Real.exp (-u) * u ^ s) (Set.Ioi 0) := by
  have hi := Real.GammaIntegral_convergent (show 0 < s + 1 by linarith)
  simpa only [add_sub_cancel_right] using hi

theorem slowKernelSpatialDerivative_majorant (q : ℂ) (m : ℕ) (c : ℝ) (hc : 0 < c)
    (x : ℂ) (hx : c ≤ x.re) {u : ℝ} (hu : 0 < u) :
    ‖slowKernelSpatialDerivative q m x u‖ ≤
      (‖(m : ℂ) - 1 - q‖ / c ^ 2 * Real.exp (Real.pi * |q.im|) *
        (1 + c⁻¹) ^ (max ((m : ℂ) - 2 - q).re 0)) *
      (Real.exp (-u) * u ^ q.re +
        Real.exp (-u) * u ^ (q.re + max ((m : ℂ) - 2 - q).re 0)) := by
  let r : ℂ := (m : ℂ) - 2 - q
  let a : ℝ := max r.re 0
  have hbounds := one_add_real_div_bounds_of_re x c hc hx hu.le
  have hxc : c ≤ ‖x‖ := hx.trans (Complex.re_le_norm x)
  have hr : Real.exp (Real.pi * |r.im|) = Real.exp (Real.pi * |q.im|) := by
    simp [r]
  have hp := (norm_cpow_le_rpow_max (1 + (u : ℂ) / x) r hbounds.1).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hbounds.2 (le_max_right _ _))
      (Real.exp_pos _).le)
  rw [hr] at hp
  have hpref : ‖(m : ℂ) - 1 - q‖ / ‖x‖ ^ 2 ≤ ‖(m : ℂ) - 1 - q‖ / c ^ 2 := by
    gcongr
  have hpowa : u ^ (q.re - 1) * u = u ^ q.re := by
    calc
      _ = u ^ (q.re - 1) * u ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = u ^ (q.re - 1 + 1) := (Real.rpow_add hu _ _).symm
      _ = _ := by congr 1; ring
  calc
    ‖slowKernelSpatialDerivative q m x u‖ =
        (‖(m : ℂ) - 1 - q‖ / ‖x‖ ^ 2) * Real.exp (-u) * u ^ q.re *
          ‖(1 + (u : ℂ) / x) ^ r‖ := by
      simp only [slowKernelSpatialDerivative, norm_mul, norm_div, norm_neg, norm_pow,
        Complex.norm_exp, Complex.neg_re, Complex.ofReal_re,
        Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.sub_re, Complex.one_re,
        Complex.norm_of_nonneg hu.le]
      rw [← hpowa]
      ring
    _ ≤ (‖(m : ℂ) - 1 - q‖ / c ^ 2) * Real.exp (-u) * u ^ q.re *
          (Real.exp (Real.pi * |q.im|) * (1 + u / c) ^ a) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le)
          (Real.rpow_nonneg hu.le _)) hp (norm_nonneg _)
            (by positivity)
    _ ≤ (‖(m : ℂ) - 1 - q‖ / c ^ 2) * Real.exp (-u) * u ^ q.re *
          (Real.exp (Real.pi * |q.im|) * ((1 + c⁻¹) ^ a * (1 + u ^ a))) := by
      gcongr
      exact one_add_div_rpow_le c a u hc (le_max_right _ _) hu.le
    _ = _ := by
      change _ = (‖(m : ℂ) - 1 - q‖ / c ^ 2 * Real.exp (Real.pi * |q.im|) *
        (1 + c⁻¹) ^ a) * (Real.exp (-u) * u ^ q.re + Real.exp (-u) * u ^ (q.re + a))
      rw [Real.rpow_add hu]
      ring

/-- Spatial derivatives have a single integrable majorant on each closed
right half-plane away from zero. -/
theorem exists_slowKernelSpatialDerivative_majorant (q : ℂ) (m : ℕ)
    (hq : -1 < q.re) (c : ℝ) (hc : 0 < c) :
    ∃ bound : ℝ → ℝ, IntegrableOn bound (Set.Ioi 0) ∧
      ∀ x : ℂ, c ≤ x.re → ∀ u : ℝ, 0 < u → ‖slowKernelSpatialDerivative q m x u‖ ≤ bound u := by
  let a : ℝ := max ((m : ℂ) - 2 - q).re 0
  let C : ℝ := ‖(m : ℂ) - 1 - q‖ / c ^ 2 * Real.exp (Real.pi * |q.im|) * (1 + c⁻¹) ^ a
  refine ⟨fun u => C * (Real.exp (-u) * u ^ q.re + Real.exp (-u) * u ^ (q.re + a)), ?_, ?_⟩
  · apply Integrable.const_mul
    exact (integrable_exp_neg_mul_rpow q.re hq).add
      (integrable_exp_neg_mul_rpow (q.re + a) (by
        have : 0 ≤ a := le_max_right _ _
        linarith))
  · intro x hx u hu
    exact slowKernelSpatialDerivative_majorant q m c hc x hx hu

end DefocusingNLS

end OAI
