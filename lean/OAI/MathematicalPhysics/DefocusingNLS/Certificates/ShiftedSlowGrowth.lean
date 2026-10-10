import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ShiftedSlowSolution
import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowGrowth
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.LaguerreProjection
import Mathlib.Analysis.Complex.Asymptotics

namespace OAI

/-! # Weighted integrability of the shifted slow solution

Every spatial derivative has polynomial growth along the translated positive
ray. Exponential weighting therefore makes its product with any polynomial
integrable, as required in the Laguerre projection.
-/

open Filter Topology Asymptotics MeasureTheory Set Polynomial

namespace DefocusingNLS

noncomputable def shiftedSlowDerivative (n : ℕ) (q : ℂ) (m : ℕ) (s : ℂ) (t : ℝ) : ℂ :=
  iteratedDeriv n (regularizedSlowSolution q m) ((t : ℂ) - s)

@[simp] theorem shiftedSlowDerivative_zero (q : ℂ) (m : ℕ) (s : ℂ) :
    shiftedSlowDerivative 0 q m s = shiftedSlowSolution q m s := rfl

theorem hasDerivAt_shiftedSlowDerivative (n : ℕ) (q : ℂ) (m : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hs : s.im ≠ 0) (t : ℝ) :
    HasDerivAt (shiftedSlowDerivative n q m s)
      (shiftedSlowDerivative (n + 1) q m s t) t := by
  have ha := (analyticOnNhd_regularizedSlowSolution_slit q m hq).iterated_deriv n
  rw [← iteratedDeriv_eq_iterate] at ha
  have hh := (ha _ (shifted_argument_mem_slitPlane s hs t)).differentiableAt.hasDerivAt
  rw [← iteratedDeriv_succ] at hh
  have h := (hh.comp (t : ℂ) ((hasDerivAt_id (t : ℂ)).sub_const s)).comp_ofReal
  convert! h using 1
  simp only [shiftedSlowDerivative, mul_one]

theorem continuous_shiftedSlowDerivative (n : ℕ) (q : ℂ) (m : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hs : s.im ≠ 0) : Continuous (shiftedSlowDerivative n q m s) :=
  continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_shiftedSlowDerivative n q m s hq hs t).continuousAt

theorem shiftedSlowDerivative_isBigO_rpow (n : ℕ) (q : ℂ) (m : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hs : s.re = 0) :
    shiftedSlowDerivative n q m s =O[atTop]
      (fun t : ℝ => t ^ (max (-(q + n).re) 0)) := by
  let a := max (-(q + n).re) 0
  obtain ⟨C, hC, hb⟩ := iteratedDeriv_regularizedSlowSolution_polynomial_bound n q m hq
  refine isBigO_iff.mpr ⟨C * (1 + ‖s‖) ^ a, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hxre : ((t : ℂ) - s).re = t := by simp [hs]
  have hxnorm : 1 ≤ ‖(t : ℂ) - s‖ :=
    ht.trans (by simpa [hxre] using Complex.re_le_norm ((t : ℂ) - s))
  have hxn : ‖(t : ℂ) - s‖ ≤ (1 + ‖s‖) * t := by
    calc
      _ ≤ ‖(t : ℂ)‖ + ‖s‖ := norm_sub_le _ _
      _ = t + ‖s‖ := by rw [Complex.norm_of_nonneg ht0]
      _ ≤ (1 + ‖s‖) * t := by nlinarith [norm_nonneg s]
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht0 _)]
  calc
    _ ≤ C * ‖(t : ℂ) - s‖ ^ a := hb _ (by simpa [hxre] using ht0) hxnorm
    _ ≤ C * ((1 + ‖s‖) * t) ^ a :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hxn (le_max_right _ _)) hC
    _ = _ := by rw [Real.mul_rpow (by positivity) ht0]; ring

theorem polynomial_eval_isBigO_exp (p : ℂ[X]) (a : ℝ) (ha : 0 < a) :
    (fun t : ℝ => p.eval (t : ℂ)) =O[atTop] (fun t : ℝ => Real.exp (a * t)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using hp.add hq
  | monomial n c =>
      have h : (fun t : ℝ => (t : ℂ) ^ n) =O[atTop]
          (fun t : ℝ => Real.exp (a * t)) := by
        simpa only [← Complex.ofReal_pow, Complex.isBigO_ofReal_left,
          Real.rpow_natCast] using (isLittleO_rpow_exp_pos_mul_atTop (n : ℝ) ha).isBigO
      simpa only [Polynomial.eval_monomial] using h.const_mul_left c

theorem integrableOn_exp_neg_mul_polynomial_of_growth (f : ℝ → ℂ) (p : ℂ[X]) (r : ℝ)
    (hc : ContinuousOn f (Ici 0)) (hf : f =O[atTop] (fun t : ℝ => t ^ r)) :
    IntegrableOn (fun t : ℝ => (Real.exp (-t) : ℂ) * f t * p.eval (t : ℂ)) (Ioi 0) := by
  have hfe : f =O[atTop] (fun t : ℝ => Real.exp ((1 / 4) * t)) :=
    hf.trans (isLittleO_rpow_exp_pos_mul_atTop r (by norm_num : 0 < (1 / 4 : ℝ))).isBigO
  have hp := polynomial_eval_isBigO_exp p (1 / 4) (by norm_num)
  have hprod : (fun t : ℝ => f t * p.eval (t : ℂ)) =O[atTop]
      (fun t : ℝ => Real.exp ((1 / 2) * t)) := by
    convert hfe.mul hp using 1
    funext t
    rw [← Real.exp_add]
    congr 1
    ring
  have hcp : ContinuousOn (fun t : ℝ => f t * p.eval (t : ℂ)) (Ici 0) := by
    apply hc.mul
    exact (p.continuous.comp Complex.continuous_ofReal).continuousOn
  have hi := integrableOn_exp_neg_smul_of_isBigO_exp
    (hcp.locallyIntegrableOn measurableSet_Ici) hprod (by norm_num : (1 / 2 : ℝ) < 1)
  have hi' := hi.mono_set Ioi_subset_Ici_self
  convert! hi' using 1
  funext t
  simp only [neg_mul, one_mul, Complex.real_smul]
  ring

theorem integrableOn_laguerreIntegrand_shiftedSlowDerivative
    (n j : ℕ) (q : ℂ) (m : ℕ) (s : ℂ)
    (hq : -1 < q.re) (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    IntegrableOn (laguerreIntegrand (shiftedSlowDerivative n q m s) j) (Ioi 0) :=
  integrableOn_exp_neg_mul_polynomial_of_growth _ _ _
    (continuous_shiftedSlowDerivative n q m s hq hsim).continuousOn
    (shiftedSlowDerivative_isBigO_rpow n q m s hq hsre)

end DefocusingNLS

end OAI
