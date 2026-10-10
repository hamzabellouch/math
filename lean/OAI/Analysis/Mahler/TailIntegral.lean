import OAI.Analysis.Mahler.PlanarEstimates
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

namespace SymmetricMahler
open Real MeasureTheory Set

lemma inverse_sqrt_eq_rpow {x : ℝ} (hx : 0 ≤ x) :
    1 / sqrt x = x ^ (-(1/2 : ℝ)) := by
  rw [one_div, sqrt_eq_rpow, rpow_neg hx]

lemma inverse_sqrt_integrable {b : ℝ} (hb : 0 ≤ b) :
    IntervalIntegrable (fun x : ℝ => 1 / sqrt x) volume 0 b := by
  have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := b)
    (r := -(1/2 : ℝ)) (by norm_num)
  apply h.congr
  intro x hx
  rw [uIoc_of_le hb] at hx
  exact (inverse_sqrt_eq_rpow hx.1.le).symm

lemma inverse_sqrt_integral {b : ℝ} (hb : 0 ≤ b) :
    (∫ x in (0 : ℝ)..b, 1 / sqrt x) = 2 * sqrt b := by
  calc
    (∫ x in (0 : ℝ)..b, 1 / sqrt x) = ∫ x in (0 : ℝ)..b, x ^ (-(1/2 : ℝ)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hb] at hx
      exact inverse_sqrt_eq_rpow hx.1
    _ = (b ^ (-(1/2 : ℝ)+1) - (0 : ℝ) ^ (-(1/2 : ℝ)+1)) / (-(1/2 : ℝ)+1) :=
      integral_rpow (Or.inl (by norm_num))
    _ = 2 * sqrt b := by
      norm_num [← sqrt_eq_rpow]
      ring

lemma shifted_inverse_sqrt_integrable {a L : ℝ} (haL : a ≤ L) :
    IntervalIntegrable (fun t : ℝ => 1 / sqrt (L-t)) volume a L := by
  have h := (inverse_sqrt_integrable (sub_nonneg.mpr haL)).comp_sub_left L
  convert h.symm using 1 <;> ring

lemma shifted_inverse_sqrt_integral {a L : ℝ} (haL : a ≤ L) :
    (∫ t in a..L, 1 / sqrt (L-t)) = 2 * sqrt (L-a) := by
  rw [intervalIntegral.integral_comp_sub_left (fun u : ℝ => 1 / sqrt u) L]
  simpa using inverse_sqrt_integral (sub_nonneg.mpr haL)

/-- The singular tail integral is well-defined even at its upper endpoint. -/
theorem tail_integrable {L : ℝ} (hL : 0 < L) :
    IntervalIntegrable (fun t : ℝ => exp (-t) * sqrt (t/(L-t))) volume 0 L := by
  have h := (shifted_inverse_sqrt_integrable (a := 0) hL.le).continuousOn_mul
    (show ContinuousOn (fun t : ℝ => exp (-t) * sqrt t) (uIcc 0 L) from
      (by fun_prop : Continuous (fun t : ℝ => exp (-t) * sqrt t)).continuousOn)
  apply h.congr
  intro t ht
  rw [uIoc_of_le hL.le] at ht
  dsimp only
  rw [sqrt_div ht.1.le]
  ring

end SymmetricMahler

namespace SymmetricMahler
open Real MeasureTheory Set

/-- The uniform-L integral estimate,
including integrability at the singular endpoint. -/
theorem uniform_tail_integral {L : ℝ} (hL : 0 < L) :
    (∫ t in (0 : ℝ)..L, exp (-t) * sqrt (t/(L-t))) ≤ 1 + 4/exp 1 := by
  have hhalf : 0 ≤ L/2 := by linarith
  have hhalfL : L/2 ≤ L := by linarith
  have hfull := tail_integrable hL
  have hfirst : IntervalIntegrable (fun t : ℝ => exp (-t)*sqrt (t/(L-t))) volume 0 (L/2) :=
    hfull.mono_set (by
      intro t ht
      rw [uIcc_of_le hhalf] at ht
      rw [uIcc_of_le hL.le]
      exact ⟨ht.1, le_trans ht.2 hhalfL⟩)
  have hsecond : IntervalIntegrable (fun t : ℝ => exp (-t)*sqrt (t/(L-t))) volume (L/2) L :=
    hfull.mono_set (by
      intro t ht
      rw [uIcc_of_le hhalfL] at ht
      rw [uIcc_of_le hL.le]
      exact ⟨le_trans hhalf ht.1, ht.2⟩)
  have hexp : IntervalIntegrable (fun t : ℝ => exp (-t)) volume 0 (L/2) :=
    (by fun_prop : Continuous (fun t : ℝ => exp (-t))).intervalIntegrable _ _
  have hfirst_bound : (∫ t in (0 : ℝ)..L/2, exp (-t)*sqrt (t/(L-t))) ≤ 1 := by
    calc
      _ ≤ ∫ t in (0 : ℝ)..L/2, exp (-t) :=
        intervalIntegral.integral_mono_on hhalf hfirst hexp
          (fun t ht => tail_first_half hL ht.1 ht.2)
      _ = 1-exp (-(L/2)) := by
        rw [intervalIntegral.integral_comp_neg exp, integral_exp]
        simp
      _ ≤ 1 := by linarith [exp_pos (-(L/2))]
  have hinv := shifted_inverse_sqrt_integrable (a := L/2) hhalfL
  have hmajor := hinv.const_mul (exp (-L/2)*sqrt L)
  have hsecond_bound : (∫ t in L/2..L, exp (-t)*sqrt (t/(L-t))) ≤
      2*L*exp (-L/2) := by
    calc
      _ ≤ ∫ t in L/2..L, (exp (-L/2)*sqrt L)*(1/sqrt (L-t)) := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo hhalfL hsecond hmajor
        intro t ht
        simpa only [mul_one_div] using tail_second_half hL ht.1.le ht.2
      _ = (exp (-L/2)*sqrt L)*(2*sqrt (L-L/2)) := by
        rw [intervalIntegral.integral_const_mul, shifted_inverse_sqrt_integral hhalfL]
      _ ≤ (exp (-L/2)*sqrt L)*(2*sqrt L) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hh : sqrt (L-L/2) ≤ sqrt L := sqrt_le_sqrt (by linarith)
        linarith
      _ = 2*L*exp (-L/2) := by
        calc
          _ = 2 * exp (-L/2) * (sqrt L)^2 := by ring
          _ = 2*L*exp (-L/2) := by rw [sq_sqrt hL.le]; ring
  rw [← intervalIntegral.integral_add_adjacent_intervals hfirst hsecond]
  exact le_trans (add_le_add hfirst_bound hsecond_bound) (uniform_tail_constant L)

end SymmetricMahler

namespace SymmetricMahler
open Real MeasureTheory

lemma rescaled_tail_ratio {m b : ℝ} (hm : m ≠ 0) (r : ℝ) :
    (m-m*r)/(m*(1-b)-(m-m*r)) = (1-r)/(r-b) := by
  rw [show m*(1-b)-(m-m*r) = m*(r-b) by ring,
    show m-m*r = m*(1-r) by ring, mul_div_mul_left _ _ hm]

/-- The change of variables t=m(1-r) in the error tail, with
normalization factors and endpoint orientations. -/
theorem rescaled_tail_integral {m b : ℝ} (hm : 0 < m) :
    (∫ r in b..(1 : ℝ), m*exp (-m*(1-r))*sqrt ((1-r)/(r-b))) =
      ∫ t in (0 : ℝ)..m*(1-b), exp (-t)*sqrt (t/(m*(1-b)-t)) := by
  let K : ℝ → ℝ := fun t => exp (-t)*sqrt (t/(m*(1-b)-t))
  have hfun : (fun r : ℝ => m*K (m-m*r)) =
      (fun r : ℝ => m*exp (-m*(1-r))*sqrt ((1-r)/(r-b))) := by
    funext r
    dsimp [K]
    rw [rescaled_tail_ratio hm.ne', show -(m-m*r) = -m*(1-r) by ring]
    ring
  rw [← hfun, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_mul K hm.ne' m]
  simp only [smul_eq_mul, mul_one, sub_self]
  rw [← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul]
  congr 1
  ring

/-- Integrability also survives the affine rescaling in the error estimate. -/
theorem rescaled_tail_integrable {m b : ℝ} (hm : 0 < m) (hb : b < 1) :
    IntervalIntegrable
      (fun r : ℝ => m*exp (-m*(1-r))*sqrt ((1-r)/(r-b))) volume b 1 := by
  have hL : 0 < m*(1-b) := mul_pos hm (sub_pos.mpr hb)
  have h := ((tail_integrable hL).comp_sub_left m).symm.comp_mul_left (c := m)
  have hlower : (m-m*(1-b))/m = b := by field_simp; ring
  simp only [sub_zero, hlower, div_self hm.ne'] at h
  have h' := h.const_mul m
  apply h'.congr
  intro r _
  dsimp only
  rw [rescaled_tail_ratio hm.ne', show -(m-m*r) = -m*(1-r) by ring]
  ring

/-- The uniform bound after substitution, independent of b and m. -/
theorem rescaled_tail_bound {m b : ℝ} (hm : 0 < m) (hb : b < 1) :
    (∫ r in b..(1 : ℝ), m*exp (-m*(1-r))*sqrt ((1-r)/(r-b))) ≤
      1 + 4/exp 1 := by
  rw [rescaled_tail_integral hm]
  exact uniform_tail_integral (mul_pos hm (sub_pos.mpr hb))

end SymmetricMahler

namespace SymmetricMahler
open Real MeasureTheory

lemma right_inverse_sqrt_integrable {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (fun r : ℝ => 1/sqrt (r-a)) volume a b := by
  have h := (inverse_sqrt_integrable (sub_nonneg.mpr hab)).comp_sub_right a
  convert h using 1 <;> ring

lemma right_inverse_sqrt_integral {a b : ℝ} (hab : a ≤ b) :
    (∫ r in a..b, 1/sqrt (r-a)) = 2*sqrt (b-a) := by
  rw [intervalIntegral.integral_comp_sub_right (fun u : ℝ => 1/sqrt u) a]
  simpa using inverse_sqrt_integral (sub_nonneg.mpr hab)

end SymmetricMahler

end OAI
