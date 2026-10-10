import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowBoundaryEquation
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! # A uniform first-order bound for the outgoing slow asymptotic -/

open MeasureTheory

namespace DefocusingNLS

theorem one_add_real_div_bounds_large (x : ℂ) (hx : 0 ≤ x.re) (hxnorm : 1 ≤ ‖x‖)
    {u : ℝ} (hu : 0 ≤ u) :
    1 ≤ ‖1 + (u : ℂ) / x‖ ∧ ‖1 + (u : ℂ) / x‖ ≤ 1 + u := by
  constructor
  · apply le_trans (b := (1 + (u : ℂ) / x).re) _ (Complex.re_le_norm _)
    simp only [Complex.add_re, Complex.one_re, Complex.div_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, zero_div, add_zero]
    have : 0 ≤ u * x.re / Complex.normSq x :=
      div_nonneg (mul_nonneg hu hx) (Complex.normSq_nonneg x)
    linarith
  · calc
      ‖1 + (u : ℂ) / x‖ ≤ 1 + u / ‖x‖ := by
        simpa only [norm_one, norm_div, Complex.norm_of_nonneg hu] using
          norm_add_le (1 : ℂ) ((u : ℂ) / x)
      _ ≤ 1 + u / 1 := by gcongr
      _ = _ := by ring

theorem hasDerivAt_regularizingBracket_real (r x : ℂ) (hx : 0 ≤ x.re)
    {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (fun v : ℝ => regularizingBracket r x v)
      (r * (1 + (u : ℂ) / x) ^ (r - 1) / x) u := by
  have h := ((((hasDerivAt_id (u : ℂ)).div_const x).const_add 1).cpow_const
    (c := r) (one_add_real_div_mem_slitPlane x hx hu)).sub_const 1
  convert! h.comp_ofReal using 1
  simp only [id_eq, one_div]
  ring

theorem regularizingBracket_uniform_bound (r x : ℂ) (hx : 0 ≤ x.re)
    (hxnorm : 1 ≤ ‖x‖) {u : ℝ} (hu : 0 ≤ u) :
    ‖regularizingBracket r x u‖ ≤
      (‖r‖ * Real.exp (Real.pi * |r.im|) / ‖x‖) *
        u * (1 + u) ^ (max (r - 1).re 0) := by
  let a : ℝ := max (r - 1).re 0
  let C : ℝ := ‖r‖ * Real.exp (Real.pi * |r.im|) / ‖x‖ * (1 + u) ^ a
  have hd (v : ℝ) (hv : v ∈ Set.Icc 0 u) :=
    hasDerivAt_regularizingBracket_real r x hx hv.1
  have hb (v : ℝ) (hv : v ∈ Set.Ico 0 u) :
      ‖r * (1 + (v : ℂ) / x) ^ (r - 1) / x‖ ≤ C := by
    have hvb := one_add_real_div_bounds_large x hx hxnorm hv.1
    have hp := norm_cpow_le_rpow_max (1 + (v : ℂ) / x) (r - 1) hvb.1
    have him : (r - 1).im = r.im := by simp
    rw [him] at hp
    have hp' : ‖(1 + (v : ℂ) / x) ^ (r - 1)‖ ≤
        Real.exp (Real.pi * |r.im|) * (1 + u) ^ a := by
      apply hp.trans
      gcongr
      exact hvb.2.trans (by linarith [hv.2])
    calc
      _ = ‖r‖ * ‖(1 + (v : ℂ) / x) ^ (r - 1)‖ / ‖x‖ := by rw [norm_div, norm_mul]
      _ ≤ ‖r‖ * (Real.exp (Real.pi * |r.im|) * (1 + u) ^ a) / ‖x‖ := by gcongr
      _ = C := by dsimp [C]; ring
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun v hv => (hd v hv).hasDerivWithinAt) hb u (show u ∈ Set.Icc 0 u from ⟨hu, le_rfl⟩)
  simp only [regularizingBracket, Complex.ofReal_zero, zero_div, add_zero,
    Complex.one_cpow, sub_self, sub_zero] at h
  calc
    _ ≤ C * u := h
    _ = _ := by dsimp [C, a]; ring

theorem regularizedSlowKernel_uniform_bound (q : ℂ) (m : ℕ) (x : ℂ)
    (hx : 0 ≤ x.re) (hxnorm : 1 ≤ ‖x‖) {u : ℝ} (hu : 0 < u) :
    ‖regularizedSlowKernel q m x u‖ ≤
      (‖(m : ℂ) - 1 - q‖ * Real.exp (Real.pi * |q.im|) *
        2 ^ (max ((m : ℂ) - 2 - q).re 0) / ‖x‖) *
      (Real.exp (-u) * u ^ q.re +
        Real.exp (-u) * u ^ (q.re + max ((m : ℂ) - 2 - q).re 0)) := by
  let r : ℂ := (m : ℂ) - 1 - q
  let a : ℝ := max ((m : ℂ) - 2 - q).re 0
  have hr : max (r - 1).re 0 = a := by
    have he : r - 1 = (m : ℂ) - 2 - q := by dsimp [r]; ring
    rw [he]
  have him : |r.im| = |q.im| := by simp [r]
  have hb := regularizingBracket_uniform_bound r x hx hxnorm hu.le
  rw [hr, him] at hb
  have hpowa : u ^ (q.re - 1) * u = u ^ q.re := by
    calc
      _ = u ^ (q.re - 1) * u ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = u ^ (q.re - 1 + 1) := (Real.rpow_add hu _ _).symm
      _ = _ := by congr 1; ring
  have hp : (1 + u) ^ a ≤ (2 : ℝ) ^ a * (1 + u ^ a) := by
    simpa only [div_one, inv_one, show (1 : ℝ) + 1 = 2 by norm_num] using
      one_add_div_rpow_le 1 a u zero_lt_one (le_max_right _ _) hu.le
  calc
    ‖regularizedSlowKernel q m x u‖ = Real.exp (-u) * u ^ (q.re - 1) *
        ‖regularizingBracket r x u‖ := by
      simp only [regularizedSlowKernel, r, norm_mul, Complex.norm_exp, Complex.neg_re,
        Complex.ofReal_re, Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.sub_re,
        Complex.one_re]
    _ ≤ Real.exp (-u) * u ^ (q.re - 1) *
        ((‖r‖ * Real.exp (Real.pi * |q.im|) / ‖x‖) * u * (1 + u) ^ a) := by gcongr
    _ = (‖r‖ * Real.exp (Real.pi * |q.im|) / ‖x‖) *
        Real.exp (-u) * u ^ q.re * (1 + u) ^ a := by rw [← hpowa]; ring
    _ ≤ (‖r‖ * Real.exp (Real.pi * |q.im|) / ‖x‖) *
        Real.exp (-u) * u ^ q.re * ((2 : ℝ) ^ a * (1 + u ^ a)) := by gcongr
    _ = _ := by change _ = (‖r‖ * Real.exp (Real.pi * |q.im|) * 2 ^ a / ‖x‖) * _
                rw [Real.rpow_add hu]
                ring

/-- The first outgoing asymptotic is uniform up to both imaginary rays. -/
theorem regularizedSlowSolution_first_remainder (q : ℂ) (m : ℕ) (hq : -1 < q.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℂ, 0 ≤ x.re → 1 ≤ ‖x‖ →
      ‖x ^ q * regularizedSlowSolution q m x - 1‖ ≤ C / ‖x‖ := by
  let a : ℝ := max ((m : ℂ) - 2 - q).re 0
  let S : ℝ → ℝ := fun u => Real.exp (-u) * u ^ q.re + Real.exp (-u) * u ^ (q.re + a)
  let A : ℝ := ‖(m : ℂ) - 1 - q‖ * Real.exp (Real.pi * |q.im|) * 2 ^ a
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hi : IntegrableOn S (Set.Ioi 0) := by
    apply (integrable_exp_neg_mul_rpow q.re hq).add
    apply integrable_exp_neg_mul_rpow
    have : 0 ≤ a := le_max_right _ _
    linarith
  have hS : 0 ≤ ∫ u : ℝ in Set.Ioi 0, S u := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu' : 0 ≤ u := le_of_lt hu
    dsimp [S]
    positivity
  refine ⟨‖(Complex.Gamma q)⁻¹‖ * A * (∫ u : ℝ in Set.Ioi 0, S u),
    mul_nonneg (mul_nonneg (norm_nonneg _) hA) hS, ?_⟩
  intro x hx hxnorm
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (zero_lt_one.trans_le hxnorm).ne'
  have hI : ‖∫ u : ℝ in Set.Ioi 0, regularizedSlowKernel q m x u‖ ≤
      (A / ‖x‖) * (∫ u : ℝ in Set.Ioi 0, S u) := by
    calc
      _ ≤ ∫ u : ℝ in Set.Ioi 0, (A / ‖x‖) * S u := by
        apply norm_integral_le_of_norm_le (hi.const_mul (A / ‖x‖))
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact regularizedSlowKernel_uniform_bound q m x hx hxnorm hu
      _ = _ := integral_const_mul _ _
  have hp : x ^ q * x ^ (-q) = 1 := by
    rw [← Complex.cpow_add _ _ hx0, add_neg_cancel, Complex.cpow_zero]
  unfold regularizedSlowSolution
  rw [← mul_assoc, hp, one_mul, add_sub_cancel_left, norm_mul]
  calc
    _ ≤ ‖(Complex.Gamma q)⁻¹‖ * ((A / ‖x‖) * (∫ u : ℝ in Set.Ioi 0, S u)) :=
      mul_le_mul_of_nonneg_left hI (norm_nonneg _)
    _ = _ := by ring

/-- The outgoing solution cannot vanish at any sufficiently large point
of the closed right half-plane. -/
theorem regularizedSlowSolution_nonzero_at_large_norm (q : ℂ) (m : ℕ)
    (hq : -1 < q.re) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : ℂ, 0 ≤ x.re → R ≤ ‖x‖ →
      regularizedSlowSolution q m x ≠ 0 := by
  obtain ⟨C, hC, hbound⟩ := regularizedSlowSolution_first_remainder q m hq
  refine ⟨2 * C + 1, by linarith, ?_⟩
  intro x hx hxnorm hz
  have hn : 1 ≤ ‖x‖ := by linarith
  have hp : 0 < ‖x‖ := zero_lt_one.trans_le hn
  have h := hbound x hx hn
  rw [hz, mul_zero, zero_sub, norm_neg, norm_one] at h
  have h' := (le_div_iff₀ hp).mp h
  nlinarith

end DefocusingNLS

end OAI
