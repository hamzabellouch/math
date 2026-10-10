import OAI.Geometry.IsometricImmersion.Pulses.PulseMomentError
import OAI.Geometry.IsometricImmersion.Caps.EnergyCauchySchwarz
import OAI.Geometry.IsometricImmersion.Pulses.PulseDerivativeBounds

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Hyperbolic

theorem pulseTest_contDiff (a tau : ℝ) : ContDiff ℝ ∞ (pulseTest a tau) :=
  (axisBump_contDiff a).mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))

theorem pulseTest_hasDerivAt (a tau x : ℝ) :
    HasDerivAt (pulseTest a tau)
      (deriv (axisBump a) x*Real.cos (tau*x)-tau*axisBump a x*Real.sin (tau*x)) x := by
  have hχ := ((axisBump_contDiff a).differentiable (by simp) x).hasDerivAt
  have hc := (Real.hasDerivAt_cos (tau*x)).comp x ((hasDerivAt_id x).const_mul tau)
  have h := hχ.mul hc
  simp only [Function.comp_def,mul_one] at h
  convert h using 1 <;> (first | rfl | ring)

theorem pulseTest_deriv (a tau x : ℝ) :
    deriv (pulseTest a tau) x =
      deriv (axisBump a) x*Real.cos (tau*x)-tau*axisBump a x*Real.sin (tau*x) :=
  (pulseTest_hasDerivAt a tau x).deriv

def pulseTestDerivativeBound (a : ℝ) (ha : 0 < a) : ℝ :=
  axisBumpDerivativeBound a ha 1+axisBumpDerivativeBound a ha 0

theorem pulseTestDerivativeBound_nonneg {a : ℝ} (ha : 0 < a) :
    0 ≤ pulseTestDerivativeBound a ha :=
  add_nonneg (axisBumpDerivativeBound_pos ha 1).le (axisBumpDerivativeBound_pos ha 0).le

theorem pulseTest_deriv_bound {a tau : ℝ} (ha : 0 < a) (ht : 1 ≤ tau) (x : ℝ) :
    |deriv (pulseTest a tau) x| ≤ pulseTestDerivativeBound a ha*tau := by
  have hA0 := (axisBumpDerivativeBound_pos ha 0).le
  have hA1 := (axisBumpDerivativeBound_pos ha 1).le
  have hχ : |axisBump a x| ≤ axisBumpDerivativeBound a ha 0 := by
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using axisBump_derivative_le ha 0 x
  have hχ' : |deriv (axisBump a) x| ≤ axisBumpDerivativeBound a ha 1 := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_one,Real.norm_eq_abs]
      using axisBump_derivative_le ha 1 x
  have ht0 : 0 ≤ tau := zero_le_one.trans ht
  rw [pulseTest_deriv]
  calc
    _ ≤ |deriv (axisBump a) x*Real.cos (tau*x)|+
        |tau*axisBump a x*Real.sin (tau*x)| := abs_sub _ _
    _ ≤ axisBumpDerivativeBound a ha 1+tau*axisBumpDerivativeBound a ha 0 := by
      apply add_le_add
      · rw [abs_mul]
        simpa only [mul_one] using mul_le_mul hχ' (Real.abs_cos_le_one _) (abs_nonneg _) hA1
      · rw [abs_mul,abs_mul,abs_of_nonneg ht0]
        simpa only [mul_one] using mul_le_mul
          (mul_le_mul_of_nonneg_left hχ ht0) (Real.abs_sin_le_one _) (abs_nonneg _) (mul_nonneg ht0 hA0)
    _ ≤ _ := by
      unfold pulseTestDerivativeBound
      nlinarith [mul_le_mul_of_nonneg_left ht hA1]

theorem real_Icc_memLp_two {f : ℝ → ℝ} {l r : ℝ} (hf : ContinuousOn f (Icc l r)) :
    MemLp f 2 (volume.restrict (Icc l r)) :=
  (memLp_two_iff_integrable_sq (hf.aestronglyMeasurable measurableSet_Icc)).mpr
    ((hf.pow 2).integrableOn_Icc)

theorem sqrt_Icc_square_le_of_abs {f : ℝ → ℝ} {l r F : ℝ}
    (hlr : l ≤ r) (hF : 0 ≤ F) (hf : ContinuousOn f (Icc l r))
    (hbound : ∀ x ∈ Icc l r, |f x| ≤ F) :
    Real.sqrt (∫ x in Icc l r, f x^2) ≤ F*Real.sqrt (r-l) := by
  have hsq : (∫ x in Icc l r, f x^2) ≤ F^2*(r-l) := by
    have hm := integral_mono_ae (μ := volume.restrict (Icc l r)) ((hf.pow 2).integrableOn_Icc)
      ((continuous_const : Continuous (fun _ : ℝ => F^2)).continuousOn.integrableOn_Icc) (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        have hh := (sq_le_sq₀ (abs_nonneg (f x)) hF).mpr (hbound x hx)
        simpa only [Pi.pow_apply,sq_abs] using hh)
    rw [setIntegral_const,Real.volume_real_Icc_of_le hlr,smul_eq_mul] at hm
    simpa only [Pi.pow_apply,mul_comm] using hm
  apply (Real.sqrt_le_sqrt hsq).trans_eq
  rw [Real.sqrt_mul (sq_nonneg F),Real.sqrt_sq_eq_abs,abs_of_nonneg hF]

theorem real_Icc_pairing_bound {f h : ℝ → ℝ} {l r F G : ℝ}
    (hlr : l ≤ r) (hF : 0 ≤ F) (hf : ContinuousOn f (Icc l r))
    (hh : ContinuousOn h (Icc l r)) (hbound : ∀ x ∈ Icc l r, |f x| ≤ F)
    (hL2 : Real.sqrt (∫ x in Icc l r, h x^2) ≤ G) :
    |∫ x in Icc l r, f x*h x| ≤ F*Real.sqrt (r-l)*G := by
  have hcs := integral_product_abs_le_sqrt_squares (real_Icc_memLp_two hf) (real_Icc_memLp_two hh)
  exact hcs.trans (mul_le_mul (sqrt_Icc_square_le_of_abs hlr hF hf hbound) hL2
    (Real.sqrt_nonneg _) (mul_nonneg hF (Real.sqrt_nonneg _)))

theorem pulse_strip_pairing_bound (i : Fin 2) {a delta tau F S0 G : ℝ}
    {test : ℝ → ℝ} {S v : Coord → ℝ} {U : Set Coord}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 0 < tau)
    (hF : 0 ≤ F) (hS0 : 0 ≤ S0) (_ : 0 ≤ G)
    (hU : IsOpen U) (hSU : pulseStrip a delta tau ⊆ U)
    (hS : ContDiffOn ℝ ∞ S U) (hv : ContDiffOn ℝ ∞ v U)
    (htest : Continuous test) (htestB : ∀ x, |test x| ≤ F)
    (hSB : ∀ p ∈ pulseStrip a delta tau, |S p| ≤ S0)
    (hL2 : ∀ theta ∈ Icc (-(delta/tau)) (delta/tau),
      Real.sqrt (∫ x in Icc (-a) a, (coordPartial i v (boxPoint x theta))^2) ≤ G) :
    |∫ theta in Icc (-(delta/tau)) (delta/tau), ∫ x in Icc (-a) a,
      test x*S (boxPoint x theta)*coordPartial i v (boxPoint x theta)| ≤
      (F*S0*Real.sqrt (2*a)*G)*(2*delta/tau) := by
  have hslice (theta : ℝ) (htheta : theta ∈ Icc (-(delta/tau)) (delta/tau)) :
      |∫ x in Icc (-a) a, test x*S (boxPoint x theta)*coordPartial i v (boxPoint x theta)| ≤
        F*S0*Real.sqrt (2*a)*G := by
    have hmap : ∀ x ∈ Icc (-a) a, boxPoint x theta ∈ U :=
      fun x hx => hSU (boxPoint_mem hx htheta)
    have hSc : ContinuousOn (fun x => S (boxPoint x theta)) (Icc (-a) a) :=
      hS.continuousOn.comp (by unfold boxPoint; fun_prop) hmap
    have hvc : ContinuousOn (fun x => coordPartial i v (boxPoint x theta)) (Icc (-a) a) :=
      (partial_contDiffOn hv hU i).continuousOn.comp (by unfold boxPoint; fun_prop) hmap
    have hproduct : ∀ x ∈ Icc (-a) a, |test x*S (boxPoint x theta)| ≤ F*S0 := by
      intro x hx
      rw [abs_mul]
      exact mul_le_mul (htestB x) (hSB _ (boxPoint_mem hx htheta)) (abs_nonneg _) hF
    have hh := real_Icc_pairing_bound (by linarith : -a ≤ a) (mul_nonneg hF hS0)
      (htest.continuousOn.mul hSc) hvc hproduct (hL2 theta htheta)
    simpa only [Pi.mul_apply,sub_neg_eq_add,←two_mul] using hh
  have htime : -(delta/tau) ≤ delta/tau := by linarith [div_nonneg hd ht.le]
  have hmajor : Integrable (fun _ : ℝ => F*S0*Real.sqrt (2*a)*G)
      (volume.restrict (Icc (-(delta/tau)) (delta/tau))) :=
    (continuous_const : Continuous
      (fun _ : ℝ => F*S0*Real.sqrt (2*a)*G)).continuousOn.integrableOn_Icc
  have hpoint : ∀ᵐ theta ∂volume.restrict (Icc (-(delta/tau)) (delta/tau)),
      ‖∫ x in Icc (-a) a, test x*S (boxPoint x theta)*coordPartial i v (boxPoint x theta)‖ ≤
        F*S0*Real.sqrt (2*a)*G := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with theta htheta
    simpa only [Real.norm_eq_abs] using hslice theta htheta
  have hi := norm_integral_le_of_norm_le hmajor hpoint
  rw [setIntegral_const,Real.volume_real_Icc_of_le htime,smul_eq_mul] at hi
  simp only [Real.norm_eq_abs] at hi
  apply hi.trans_eq
  ring

theorem pulse_derivative_pairing_delta_sq (i : Fin 2) {a delta tau S0 M : ℝ} {N : ℕ}
    {S v : Coord → ℝ} {U : Set Coord}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 1 ≤ tau)
    (hS0 : 0 ≤ S0) (hM : 0 ≤ M) (hU : IsOpen U) (hSU : pulseStrip a delta tau ⊆ U)
    (hS : ContDiffOn ℝ ∞ S U) (hv : ContDiffOn ℝ ∞ v U)
    (hSB : ∀ p ∈ pulseStrip a delta tau, |S p| ≤ S0)
    (hL2 : ∀ theta ∈ Icc (-(delta/tau)) (delta/tau),
      Real.sqrt (∫ x in Icc (-a) a, (coordPartial i v (boxPoint x theta))^2) ≤ M*delta*tau/tau^N) :
    |∫ theta in Icc (-(delta/tau)) (delta/tau), ∫ x in Icc (-a) a,
      deriv (pulseTest a tau) x*S (boxPoint x theta)*coordPartial i v (boxPoint x theta)| ≤
      (2*pulseTestDerivativeBound a ha*S0*Real.sqrt (2*a)*M)*delta^2*tau/tau^N := by
  have htpos : 0 < tau := zero_lt_one.trans_le ht
  have hF : 0 ≤ pulseTestDerivativeBound a ha*tau :=
    mul_nonneg (pulseTestDerivativeBound_nonneg ha) htpos.le
  have hG : 0 ≤ M*delta*tau/tau^N := by positivity
  have htest : Continuous (deriv (pulseTest a tau)) :=
    (contDiff_infty_iff_deriv.mp (pulseTest_contDiff a tau)).2.continuous
  have hh := pulse_strip_pairing_bound i ha hd htpos hF hS0 hG hU hSU hS hv htest
    (pulseTest_deriv_bound ha ht) hSB hL2
  apply hh.trans_eq
  field_simp [htpos.ne']

theorem pulse_test_pairing_extra_inv_tau (i : Fin 2) {a delta tau S0 M : ℝ} {N : ℕ}
    {S v : Coord → ℝ} {U : Set Coord}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 1 ≤ tau)
    (hS0 : 0 ≤ S0) (hM : 0 ≤ M) (hU : IsOpen U) (hSU : pulseStrip a delta tau ⊆ U)
    (hS : ContDiffOn ℝ ∞ S U) (hv : ContDiffOn ℝ ∞ v U)
    (hSB : ∀ p ∈ pulseStrip a delta tau, |S p| ≤ S0)
    (hL2 : ∀ theta ∈ Icc (-(delta/tau)) (delta/tau),
      Real.sqrt (∫ x in Icc (-a) a, (coordPartial i v (boxPoint x theta))^2) ≤ M*delta*tau/tau^N) :
    |∫ theta in Icc (-(delta/tau)) (delta/tau), ∫ x in Icc (-a) a,
      pulseTest a tau x*S (boxPoint x theta)*coordPartial i v (boxPoint x theta)| ≤
      (2*axisBumpDerivativeBound a ha 0*S0*Real.sqrt (2*a)*M)*delta^2/tau^N := by
  have htpos : 0 < tau := zero_lt_one.trans_le ht
  have hF := (axisBumpDerivativeBound_pos ha 0).le
  have hG : 0 ≤ M*delta*tau/tau^N := by positivity
  have htest (x : ℝ) : |pulseTest a tau x| ≤ axisBumpDerivativeBound a ha 0 := by
    have hχ : |axisBump a x| ≤ axisBumpDerivativeBound a ha 0 := by
      simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using axisBump_derivative_le ha 0 x
    exact (pulseTest_abs_le a tau x).trans ((le_abs_self _).trans hχ)
  have hh := pulse_strip_pairing_bound i ha hd htpos hF hS0 hG hU hSU hS hv
    (pulseTest_continuous a tau) htest hSB hL2
  apply hh.trans_eq
  field_simp [htpos.ne']

end SmoothLocal.Pulse

end

end OAI
