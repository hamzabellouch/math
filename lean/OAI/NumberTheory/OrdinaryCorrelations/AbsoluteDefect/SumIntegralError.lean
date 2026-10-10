import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral

namespace OrdinaryLogIntegral

theorem sum_integral_error (F F' : ℝ → ℂ) (a : ℝ) (N : ℕ) {L : ℝ}
    (hL : 0 ≤ L)
    (hF : ∀ x ∈ Set.Icc a (a+N), HasDerivAt F (F' x) x)
    (hbound : ∀ x ∈ Set.Icc a (a+N), ‖F' x‖ ≤ L) :
    ‖(∑ n ∈ Finset.range N, F (a+n)) - ∫ x in a..a+N, F x‖ ≤ N * L := by
  have hcont : ContinuousOn F (Set.Icc a (a+N)) :=
    fun x hx => (hF x hx).continuousAt.continuousWithinAt
  have hsub (n : ℕ) (hn : n < N) :
      Set.uIcc (a+n) (a+(n+1 : ℕ)) ⊆ Set.Icc a (a+N) := by
    rw [Set.uIcc_of_le (by push_cast; linarith)]
    intro x hx
    have hn' : (n+1 : ℝ) ≤ N := by exact_mod_cast hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    constructor <;> push_cast at hx <;> linarith [hx.1, hx.2]
  have hi (n : ℕ) (hn : n < N) :
      IntervalIntegrable F volume (a+n) (a+(n+1 : ℕ)) :=
    (hcont.mono (hsub n hn)).intervalIntegrable
  have hsum : (∑ n ∈ Finset.range N, ∫ x in a+n..a+(n+1 : ℕ), F x) =
      ∫ x in a..a+N, F x := by
    simpa only [Nat.cast_zero, add_zero] using
      (intervalIntegral.sum_integral_adjacent_intervals (a := fun n => a+(n : ℝ)) hi)
  rw [← hsum, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ Finset.range N, L := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' := Finset.mem_range.mp hn
      have he : F (a+n) - ∫ x in a+n..a+(n+1 : ℕ), F x =
          ∫ x in a+n..a+(n+1 : ℕ), F (a+n) - F x := by
        rw [intervalIntegral.integral_sub intervalIntegrable_const (hi n hn'),
          intervalIntegral.integral_const]
        simp only [Nat.cast_add, Nat.cast_one]
        have hh : a + ((n : ℝ)+1) - (a+n) = 1 := by ring
        rw [hh, one_smul]
      rw [he]
      have hh := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := a+(n : ℝ)) (b := a+(n+1 : ℕ)) (C := L) (f := fun x => F (a+n)-F x)
      have hlocal : ∀ x ∈ Set.uIoc (a+n) (a+(n+1 : ℕ)), ‖F (a+n)-F x‖ ≤ L := by
        intro x hx
        have hn0 : a+n ∈ Set.Icc a (a+N) := hsub n hn' (Set.left_mem_uIcc)
        have hx0 := hsub n hn' (Set.uIoc_subset_uIcc hx)
        have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
          (fun y hy => (hF y hy).hasDerivWithinAt) hbound (convex_Icc a (a+N)) hn0 hx0
        have hlen : ‖x - (a+n)‖ ≤ 1 := by
          rw [Set.uIoc_of_le (by push_cast; linarith)] at hx
          rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1])]
          push_cast at hx
          linarith [hx.2]
        rw [norm_sub_rev]
        exact hmv.trans (by nlinarith)
      simpa only [Nat.cast_add, Nat.cast_one, add_sub_add_left_eq_sub, add_sub_cancel_left,
        abs_one, mul_one] using hh hlocal
    _ = _ := by simp [mul_comm]

def logPhase (t x : ℝ) : ℂ := Complex.exp (Complex.I * (t * Real.log x : ℝ))

lemma norm_logPhase (t x : ℝ) : ‖logPhase t x‖ = 1 := by
  exact Complex.norm_exp_I_mul_ofReal _

lemma hasDerivAt_logPhase (t : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (logPhase t) (logPhase t x * (Complex.I * (t / x : ℝ))) x := by
  have hh := ((Real.hasDerivAt_log hx).const_mul t).ofReal_comp.const_mul Complex.I |>.cexp
  refine hh.congr_deriv ?_
  simp only [logPhase, div_eq_mul_inv, Complex.ofReal_mul]

def differencePhase (t h x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (t * (Real.log (x+h)-Real.log x) : ℝ))

lemma norm_differencePhase (t h x : ℝ) : ‖differencePhase t h x‖ = 1 := by
  exact Complex.norm_exp_I_mul_ofReal _

lemma hasDerivAt_differencePhase (t h : ℝ) {x : ℝ}
    (hx : x ≠ 0) (hxh : x+h ≠ 0) :
    HasDerivAt (differencePhase t h)
      (differencePhase t h x * (Complex.I * (-t*h/(x*(x+h)) : ℝ))) x := by
  have hd : HasDerivAt (fun x : ℝ => Real.log (x+h)-Real.log x)
      (-(h/(x*(x+h)))) x := by
    refine ((((hasDerivAt_id x).add_const h).log hxh).sub (Real.hasDerivAt_log hx)).congr_deriv ?_
    simp only [id_eq]
    field_simp [hx, hxh]
    ring
  have hh := (hd.const_mul t).ofReal_comp.const_mul Complex.I |>.cexp
  refine hh.congr_deriv ?_
  dsimp [differencePhase]
  congr 2
  push_cast
  ring

lemma differencePhase_eq (t h x : ℝ) :
    differencePhase t h x = logPhase t (x+h) * star (logPhase t x) := by
  simp only [differencePhase, logPhase, Complex.star_def, ← Complex.exp_conj,
    map_mul, Complex.conj_I, Complex.conj_ofReal, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma hasDerivAt_differenceMultiplier (t h : ℝ) {x : ℝ}
    (hx : x ≠ 0) (hxh : x+h ≠ 0) :
    HasDerivAt (fun y => ((y*(y+h) : ℝ) : ℂ) * differencePhase t h y)
      (((2*x+h : ℝ) : ℂ) * differencePhase t h x -
        (Complex.I * ((t*h : ℝ) : ℂ)) * differencePhase t h x) x := by
  have hh := (((hasDerivAt_id x).mul ((hasDerivAt_id x).add_const h)).ofReal_comp).mul
    (hasDerivAt_differencePhase t h hx hxh)
  refine hh.congr_deriv ?_
  simp only [id_eq, one_mul, mul_one, Pi.mul_apply]
  push_cast
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  have hxhc : (x : ℂ) + h ≠ 0 := by exact_mod_cast hxh
  field_simp
  ring

theorem difference_integral_bound (t h a b : ℝ) (ha : 0 < a)
    (hab : a ≤ b) (hh : 0 ≤ h) :
    |t*h| * ‖∫ x in a..b, differencePhase t h x‖ ≤
      b*(b+h) + a*(a+h) + (2*b+h)*(b-a) := by
  have hb : 0 < b := ha.trans_le hab
  have hp (x : ℝ) (hx : x ∈ Set.uIcc a b) : 0 < x := by
    rw [Set.uIcc_of_le hab] at hx
    exact ha.trans_le hx.1
  have hFc : ContinuousOn (differencePhase t h) (Set.uIcc a b) := by
    intro x hx
    exact (hasDerivAt_differencePhase t h (ne_of_gt (hp x hx))
      (ne_of_gt (by linarith [hp x hx]))).continuousAt.continuousWithinAt
  have hPc : ContinuousOn (fun x : ℝ => ((2*x+h : ℝ) : ℂ) * differencePhase t h x)
      (Set.uIcc a b) := by
    exact (Complex.continuous_ofReal.comp (by fun_prop)).continuousOn.mul hFc
  have hI : IntervalIntegrable (differencePhase t h) volume a b := hFc.intervalIntegrable
  have hP : IntervalIntegrable (fun x : ℝ => ((2*x+h : ℝ) : ℂ) * differencePhase t h x) volume a b := hPc.intervalIntegrable
  have hderiv := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hasDerivAt_differenceMultiplier t h (ne_of_gt (hp x hx))
      (ne_of_gt (by linarith [hp x hx])))
    (hP.sub (hI.const_mul (Complex.I * ((t*h : ℝ) : ℂ))))
  rw [intervalIntegral.integral_sub hP (hI.const_mul _),
    intervalIntegral.integral_const_mul] at hderiv
  have he : (Complex.I * ((t*h : ℝ) : ℂ)) * (∫ x in a..b, differencePhase t h x) =
      (∫ x in a..b, ((2*x+h : ℝ) : ℂ) * differencePhase t h x) -
        (((b*(b+h) : ℝ) : ℂ) * differencePhase t h b -
          ((a*(a+h) : ℝ) : ℂ) * differencePhase t h a) := by
    linear_combination -hderiv
  have hnorm (x : ℝ) (hx : 0 ≤ x) :
      ‖((x*(x+h) : ℝ) : ℂ) * differencePhase t h x‖ = x*(x+h) := by
    rw [norm_mul, norm_differencePhase, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hx (add_nonneg hx hh))]
  have hPI : ‖∫ x in a..b, ((2*x+h : ℝ) : ℂ) * differencePhase t h x‖ ≤
      (2*b+h)*(b-a) := by
    have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := 2*b+h)
      (f := fun x : ℝ => ((2*x+h : ℝ) : ℂ) * differencePhase t h x)
    rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hbnd
    apply hbnd
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    rw [norm_mul, norm_differencePhase, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [hx.1])]
    linarith [hx.2]
  calc
    _ = ‖(Complex.I * ((t*h : ℝ) : ℂ)) * (∫ x in a..b, differencePhase t h x)‖ := by
      simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    _ = _ := congrArg norm he
    _ ≤ ‖∫ x in a..b, ((2*x+h : ℝ) : ℂ) * differencePhase t h x‖ +
        (‖((b*(b+h) : ℝ) : ℂ) * differencePhase t h b‖ +
          ‖((a*(a+h) : ℝ) : ℂ) * differencePhase t h a‖) := by
      exact (norm_sub_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)
    _ ≤ _ := by rw [hnorm b hb.le, hnorm a ha.le]; linarith

theorem difference_sum_integral_error (t h a : ℝ) (N : ℕ) (ha : 0 < a) (hh : 0 ≤ h) :
    ‖(∑ n ∈ Finset.range N, differencePhase t h (a+n)) -
        ∫ x in a..a+N, differencePhase t h x‖ ≤ (N : ℝ) * (|t| *h / a^2) := by
  apply sum_integral_error (differencePhase t h)
    (fun x => differencePhase t h x * (Complex.I * (-t*h/(x*(x+h)) : ℝ))) a N
    (by positivity)
  · intro x hx
    exact hasDerivAt_differencePhase t h (ne_of_gt (ha.trans_le hx.1))
      (ne_of_gt (by linarith [hx.1]))
  · intro x hx
    have hx0 : 0 < x := ha.trans_le hx.1
    rw [norm_mul, norm_differencePhase, one_mul, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_neg,
      abs_of_nonneg hh, abs_of_pos (mul_pos hx0 (by linarith))]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith [mul_nonneg hx0.le hh, mul_nonneg (sub_nonneg.mpr hx.1) (add_nonneg hx0.le ha.le)]

theorem difference_sum_bound (t h a : ℝ) (N : ℕ) (ha : 0 < a) (hh : 0 < h)
    (ht : t ≠ 0) :
    ‖∑ n ∈ Finset.range N, differencePhase t h (a+n)‖ ≤
      ((a+N)*(a+N+h) + a*(a+h) + (2*(a+N)+h)*N)/(|t| *h) +
        (N : ℝ) * (|t| *h/a^2) := by
  have hd := difference_sum_integral_error t h a N ha hh.le
  have hi := difference_integral_bound t h a (a+N) ha (by linarith [Nat.cast_nonneg (α := ℝ) N]) hh.le
  have hth : 0 < |t| *h := mul_pos (abs_pos.mpr ht) hh
  have hI : ‖∫ x in a..a+N, differencePhase t h x‖ ≤
      ((a+N)*(a+N+h) + a*(a+h) + (2*(a+N)+h)*N)/(|t| *h) := by
    rw [le_div_iff₀ hth]
    simpa only [abs_mul, abs_of_pos hh, add_sub_cancel_left, mul_comm] using hi
  have htri := norm_add_le
    (∫ x in a..a+N, differencePhase t h x)
    ((∑ n ∈ Finset.range N, differencePhase t h (a+n))-
      ∫ x in a..a+N, differencePhase t h x)
  rw [add_sub_cancel] at htri
  exact htri.trans (add_le_add hI hd)

end OrdinaryLogIntegral

end

end OAI
