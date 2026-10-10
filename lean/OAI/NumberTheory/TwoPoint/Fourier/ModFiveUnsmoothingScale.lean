import OAI.NumberTheory.TwoPoint.Fourier.ModFiveUnsmoothing
import OAI.NumberTheory.TwoPoint.Fourier.ModFiveSmoothedDecay

namespace OAI

/-! The finite-difference step with the actual short interval length.
A ceiling is used so that both triangular cutoffs have the same fractional
part, and the resulting exponential saving only loses a fixed factor. -/

namespace TwoPointCorrelations

open Filter

lemma modFive_nonnat_add {x : ℝ} (hx : 0 ≤ x)
    (hxn : ∀ n : ℕ, x ≠ (n : ℝ)) (m : ℕ) :
    ∀ n : ℕ, x + m ≠ (n : ℝ) := by
  intro n he
  have hmn : m ≤ n := by exact_mod_cast (show (m : ℝ) ≤ n by linarith)
  apply hxn (n - m)
  rw [Nat.cast_sub hmn]
  linarith

lemma modFive_unsmoothing_numeric (χ : DirichletCharacter ℂ 5)
    {x c : ℝ} (hx : 1 ≤ x) (hc : 0 < c) {m : ℕ} (hm : 0 < m)
    (hmlow : x * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) ≤ m)
    (hmhigh : (m : ℝ) ≤ 2 * (x * Real.exp (-(c / 2) * Real.sqrt (Real.log x))))
    (hsx : ‖modFiveSmoothedPsi χ x‖ ≤ x * Real.exp (-c * Real.sqrt (Real.log x)))
    (hsy : ‖modFiveSmoothedPsi χ (x + m)‖ ≤
      (x + m) * Real.exp (-c * Real.sqrt (Real.log (x + m)))) :
    ‖modFiveTwistedPsi χ x‖ ≤
      x * (10 + 2 * Real.log (3 * x)) * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) := by
  let S := Real.sqrt (Real.log x)
  let E := Real.exp (-c * S)
  let e := Real.exp (-(c / 2) * S)
  let v := x * e
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hmp : 0 < (m : ℝ) := by exact_mod_cast hm
  have hep : 0 < e := Real.exp_pos _
  have hvp : 0 < v := mul_pos hxp hep
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (by linarith : -(c / 2) ≤ 0) hS)
  have hm2 : (m : ℝ) ≤ 2 * x := hmhigh.trans (by
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hxp.le he1) (by norm_num))
  have hy3 : x + (m : ℝ) ≤ 3 * x := by linarith
  have hyp : 0 < x + (m : ℝ) := by positivity
  have hlog : Real.log (x + m) ≤ Real.log (3 * x) :=
    Real.log_le_log hyp hy3
  have hlognonneg : 0 ≤ Real.log (3 * x) := Real.log_nonneg (by linarith)
  have hSmono : S ≤ Real.sqrt (Real.log (x + m)) :=
    Real.sqrt_le_sqrt (Real.log_le_log hxp (le_add_of_nonneg_right (Nat.cast_nonneg m)))
  have hEmono : Real.exp (-c * Real.sqrt (Real.log (x + m))) ≤ E := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hSmono (neg_nonpos.mpr hc.le)
  have hybound : ‖modFiveSmoothedPsi χ (x + m)‖ ≤ (x + m) * E :=
    hsy.trans (mul_le_mul_of_nonneg_left hEmono hyp.le)
  have hquad : (x + (m : ℝ)) ^ 2 ≤ 9 * x ^ 2 := by nlinarith
  have hnum : (x + m) * ‖modFiveSmoothedPsi χ (x + m)‖ +
      x * ‖modFiveSmoothedPsi χ x‖ ≤ 10 * x ^ 2 * E := by
    have hyb := mul_le_mul_of_nonneg_left hybound hyp.le
    have hxb := mul_le_mul_of_nonneg_left hsx hxp.le
    have hqb := mul_le_mul_of_nonneg_right hquad (Real.exp_pos (-c * S)).le
    change x * ‖modFiveSmoothedPsi χ x‖ ≤ x * (x * E) at hxb
    nlinarith
  have hupper := modFive_unsmoothing_bound χ hxp hm
  have hquot : 10 * x ^ 2 * E / (m : ℝ) ≤ 10 * x ^ 2 * E / v :=
    div_le_div_of_nonneg_left (by dsimp [E]; positivity) hvp hmlow
  have htail : (m : ℝ) * Real.log (x + m) ≤ 2 * v * Real.log (3 * x) := by
    calc
      _ ≤ (m : ℝ) * Real.log (3 * x) := mul_le_mul_of_nonneg_left hlog hmp.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hmhigh hlognonneg
  have hEe : E = e ^ 2 := by
    dsimp [E, e]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ (10 * x ^ 2 * E + (m : ℝ) ^ 2 * Real.log (x + m)) / m :=
      hupper.trans (div_le_div_of_nonneg_right (add_le_add hnum le_rfl) hmp.le)
    _ = 10 * x ^ 2 * E / m + (m : ℝ) * Real.log (x + m) := by
      field_simp
    _ ≤ 10 * x ^ 2 * E / v + 2 * v * Real.log (3 * x) := add_le_add hquot htail
    _ = _ := by
      change 10 * x ^ 2 * E / v + 2 * v * Real.log (3 * x) =
        x * (10 + 2 * Real.log (3 * x)) * e
      rw [hEe]
      dsimp [v]
      field_simp

lemma modFive_unsmoothing_scale (c : ℝ) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      1 ≤ x * Real.exp (-(c / 2) * Real.sqrt (Real.log x)) ∧
      (10 + 2 * Real.log (3 * x)) *
        Real.exp (-(c / 4) * Real.sqrt (Real.log x)) ≤ 1 := by
  have hp := modFive_perron_polynomial_absorption 16 (c / 4) (by positivity)
  have hs := (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).eventually
    ((eventually_ge_atTop (max 1 (c / 2))).and hp)
  filter_upwards [hs, eventually_ge_atTop (1 : ℝ)] with x h hx
  let S := Real.sqrt (Real.log x)
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hS1 : 1 ≤ S := (le_max_left _ _).trans h.1
  have hSc : c / 2 ≤ S := (le_max_right _ _).trans h.1
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hSsq : S ^ 2 = Real.log x := Real.sq_sqrt (Real.log_nonneg hx)
  constructor
  · have he : x * Real.exp (-(c / 2) * S) = Real.exp (S ^ 2 - (c / 2) * S) := by
      rw [hSsq, sub_eq_add_neg, Real.exp_add, Real.exp_log hxp]
      congr 1
      ring_nf
    change 1 ≤ x * Real.exp (-(c / 2) * S)
    rw [he]
    apply Real.one_le_exp
    nlinarith [mul_nonneg hS0 (sub_nonneg.mpr hSc)]
  · have hlog3 : Real.log 3 ≤ 2 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    have hcoef : 10 + 2 * Real.log (3 * x) ≤ 16 * S ^ 2 := by
      rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hxp.ne']
      nlinarith [sq_nonneg (S - 1)]
    have he : Real.exp (-(c / 4) * S) ≤ Real.exp (1 - (c / 4) * S) :=
      Real.exp_le_exp.mpr (by linarith)
    exact (mul_le_mul hcoef he (Real.exp_pos _).le (by positivity)).trans h.2

/-- The nonprincipal twisted Mangoldt sum has a quantitative exponential
saving. Nonintegral cutoffs suffice here and are removed by floor transfer. -/
theorem modFive_unsmoothed_decay_nonnat : ∃ c : ℝ, 0 < c ∧
    ∀ᶠ x : ℝ in atTop, ∀ χ : DirichletCharacter ℂ 5, χ ≠ 1 →
      (∀ n : ℕ, x ≠ (n : ℝ)) →
      ‖modFiveTwistedPsi χ x‖ ≤ x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c, hc, hs⟩ := modFive_smoothed_decay
  obtain ⟨X, hX⟩ := eventually_atTop.mp hs
  refine ⟨c / 4, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop X, eventually_ge_atTop (1 : ℝ),
    modFive_unsmoothing_scale c hc] with x hxX hx hscale χ hχ hxnat
  let S := Real.sqrt (Real.log x)
  let v := x * Real.exp (-(c / 2) * S)
  let m := ⌈v⌉₊
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hv1 : 1 ≤ v := hscale.1
  have hvp : 0 < v := zero_lt_one.trans_le hv1
  have hmlo : v ≤ (m : ℝ) := Nat.le_ceil v
  have hm : 0 < m := by
    have hmp : 0 < (m : ℝ) := hvp.trans_le hmlo
    exact_mod_cast hmp
  have hmhi : (m : ℝ) ≤ 2 * v := by
    have hh : (m : ℝ) < v + 1 := Nat.ceil_lt_add_one hvp.le
    linarith
  have hys : X ≤ x + (m : ℝ) :=
    hxX.trans (le_add_of_nonneg_right (Nat.cast_nonneg m))
  have hnum := modFive_unsmoothing_numeric χ hx hc hm hmlo hmhi
    (hX x hxX χ hχ hxnat)
    (hX (x + m) hys χ hχ (modFive_nonnat_add (by linarith) hxnat m))
  have he : x * (10 + 2 * Real.log (3 * x)) * Real.exp (-(c / 2) * S) =
      (x * Real.exp (-(c / 4) * S)) *
        ((10 + 2 * Real.log (3 * x)) * Real.exp (-(c / 4) * S)) := by
    have harg : -(c / 2) * S = -(c / 4) * S + -(c / 4) * S := by ring
    rw [harg, Real.exp_add]
    ring
  apply hnum.trans
  change x * (10 + 2 * Real.log (3 * x)) * Real.exp (-(c / 2) * S) ≤ _
  rw [he]
  exact (mul_le_mul_of_nonneg_left hscale.2 (by positivity)).trans_eq (mul_one _)

end TwoPointCorrelations

end OAI
