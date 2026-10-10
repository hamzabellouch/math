import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFrequencyTail
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTDyadicMeanSquare
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace OAI

/-! Finite-height mean-square estimates control the entire short-window
kernel. The frequencies beyond the polynomial length cost only `(T/N)^2`. -/

namespace TwoPointCorrelations

open MeasureTheory Set

lemma mrt_short_kernel_continuous (T : ℝ) : Continuous (mrtShortKernel T) := by
  exact continuous_const.min (continuous_const.div
    (continuous_const.add (continuous_id.pow 2)) (fun t => by positivity))

lemma mrt_bounded_square_tail_integrable (F : ℝ → ℝ) (hF : Continuous F)
    (hFn : ∀ t, 0 ≤ F t) {C R : ℝ} (hC : ∀ t, F t ≤ C) (hR : 0 < R) :
    IntegrableOn (fun t => (F t+F (-t))/t^2) (Ioi R) := by
  have hi : IntegrableOn (fun t : ℝ => (t^2)⁻¹) (Ioi R) := by
    apply (integrableOn_Ioi_rpow_of_lt (a := (-2:ℝ)) (by norm_num) hR).congr_fun
      (fun t ht => ?_) measurableSet_Ioi
    rw [Real.rpow_neg (hR.trans ht).le, Real.rpow_two]
  have hm : Measurable (fun t : ℝ => (F t+F (-t))/t^2) := by fun_prop
  apply (hi.const_mul (2*C)).mono' hm.aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (add_nonneg (hFn _) (hFn _))
    (sq_nonneg _))]
  calc
    _ ≤ (2*C)/t^2 := div_le_div_of_nonneg_right (by linarith [hC t, hC (-t)])
      (sq_nonneg _)
    _ = _ := by ring

lemma mrt_bounded_kernel_integrable (F : ℝ → ℝ) (hF : Continuous F)
    (hFn : ∀ t, 0 ≤ F t) {C : ℝ} (hC : ∀ t, F t ≤ C) (T : ℝ) :
    Integrable (fun t => mrtShortKernel T t * F t) := by
  apply (integrable_inv_one_add_sq.const_mul (T^2*C)).mono'
    ((mrt_short_kernel_continuous T).mul hF).aestronglyMeasurable
  filter_upwards with t
  have hk : 0 ≤ mrtShortKernel T t := le_min (by norm_num) (by positivity)
  change ‖mrtShortKernel T t * F t‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hk (hFn t))]
  calc
    _ ≤ (T^2/(1+t^2))*C := mul_le_mul (min_le_right _ _) (hC t) (hFn t)
      (by positivity)
    _ = _ := by ring

lemma mrt_integral_symmetric_halves (G : ℝ → ℝ) (hG : Integrable G) :
    (∫ t : ℝ, G t) = ∫ t in Ioi (0:ℝ), G t+G (-t) := by
  have hGn : Integrable (fun t => G (-t)) := hG.comp_neg
  rw [integral_add hG.integrableOn hGn.integrableOn,
    integral_comp_neg_Ioi, neg_zero]
  exact (intervalIntegral.integral_Iic_add_Ioi hG.integrableOn hG.integrableOn).symm.trans
    (add_comm _ _)

theorem mrt_short_kernel_finite_height (F : ℝ → ℝ) (hF : Continuous F)
    (hFn : ∀ t, 0 ≤ F t) {C N T ε A : ℝ} (hC : ∀ t, F t ≤ C)
    (hN : 0 < N) (hT : 0 < T) (hTN : T ≤ N) (hε : 0 ≤ ε) (hA : 0 ≤ A)
    (hsmall : ∀ v, T ≤ v → v ≤ N →
      (∫ t in -v..v, F t) ≤ ε*(v/N+1))
    (hglobal : ∀ v, N ≤ v → (∫ t in -v..v, F t) ≤ A*(v/N+1)) :
    (∫ t : ℝ, mrtShortKernel T t * F t) ≤ 10*ε+4*A*(T/N)^2 := by
  let G : ℝ → ℝ := fun t => mrtShortKernel T t * (F t+F (-t))
  have hKi := mrt_bounded_kernel_integrable F hF hFn hC T
  have hGi : Integrable G := by
    have he : G = fun t => mrtShortKernel T t*F t +
        (fun t => mrtShortKernel T t*F t) (-t) := by
      funext t
      simp only [G, mrtShortKernel, neg_sq]
      ring
    rw [he]
    exact hKi.add hKi.comp_neg
  have hGe : (∫ t : ℝ, mrtShortKernel T t * F t) = ∫ t in Ioi (0:ℝ), G t := by
    rw [mrt_integral_symmetric_halves _ hKi]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [G, mrtShortKernel, neg_sq]
    ring
  have hGcont : Continuous G := (mrt_short_kernel_continuous T).mul
    (hF.add (hF.comp continuous_neg))
  have hlow : (∫ t in (0:ℝ)..T, G t) ≤ 2*ε := by
    have hfi : IntervalIntegrable (fun t => F t+F (-t)) volume 0 T :=
      (hF.add (hF.comp continuous_neg)).intervalIntegrable _ _
    have hm := intervalIntegral.integral_mono_on (μ := volume) hT.le
      (hGcont.intervalIntegrable _ _) hfi
      (fun t _ => mul_le_of_le_one_left (add_nonneg (hFn _) (hFn _)) (min_le_left _ _))
    rw [mrt_symmetric_prefix F hF T] at hm
    apply hm.trans ((hsmall T le_rfl hTN).trans _)
    have hdiv : T/N ≤ 1 := (div_le_one hN).mpr hTN
    nlinarith
  have hmid : (∫ t in T..N, G t) ≤ 8*ε := by
    have hratio := mrt_frequency_tail_finite F hF hFn hT le_rfl hTN
      (mul_nonneg hε (by positivity : 0 ≤ T/N+1)) (fun v hv hvN => by
        apply (hsmall v hv hvN).trans
        have hvT : 1 ≤ v/T := (le_div_iff₀ hT).mpr (by simpa using hv)
        have he : (T/N+1)*(v/T+1)-(v/N+1) = T/N+v/T := by field_simp; ring
        calc
          ε*(v/N+1) ≤ ε*((T/N+1)*(v/T+1)) := by
            apply mul_le_mul_of_nonneg_left _ hε
            nlinarith [div_nonneg hT.le hN.le]
          _ = _ := by ring)
    have hct : ContinuousOn (fun t => (F t+F (-t))/t^2) (uIcc T N) := by
      apply (hF.add (hF.comp continuous_neg)).continuousOn.div
        (continuous_id.pow 2).continuousOn
      intro t ht
      rw [uIcc_of_le hTN] at ht
      exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hT ht.1))
    have hwi : IntervalIntegrable (fun t => T^2*((F t+F (-t))/t^2)) volume T N :=
      (hct.const_mul (T^2)).intervalIntegrable
    have hm := intervalIntegral.integral_mono_on (μ := volume) hTN
      (hGcont.intervalIntegrable _ _) hwi (fun t ht => by
          have ht0 := hT.trans_le ht.1
          have hk : mrtShortKernel T t ≤ T^2/t^2 :=
            (min_le_right _ _).trans (div_le_div_of_nonneg_left (sq_nonneg T)
              (sq_pos_of_pos ht0) (by linarith))
          calc
            G t ≤ (T^2/t^2)*(F t+F (-t)) :=
              mul_le_mul_of_nonneg_right hk (add_nonneg (hFn t) (hFn (-t)))
            _ = _ := by ring)
    rw [intervalIntegral.integral_const_mul] at hm
    have hdiv : T/N ≤ 1 := (div_le_one hN).mpr hTN
    calc
      _ ≤ T^2*(4*(ε*(T/N+1))/(T*T)) := hm.trans
        (mul_le_mul_of_nonneg_left hratio (sq_nonneg _))
      _ = 4*ε*(T/N+1) := by field_simp
      _ ≤ _ := by nlinarith
  have htaili := mrt_bounded_square_tail_integrable F hF hFn hC hN
  have htail := mrt_frequency_tail_infinite F hF hFn hN le_rfl hA hglobal htaili
  have hhigh : (∫ t in Ioi N, G t) ≤ 4*A*(T/N)^2 := by
    have hm := setIntegral_mono_on hGi.integrableOn (htaili.const_mul (T^2))
      measurableSet_Ioi (fun t ht => by
        have ht0 := hN.trans ht
        have hk : mrtShortKernel T t ≤ T^2/t^2 :=
          (min_le_right _ _).trans (div_le_div_of_nonneg_left (sq_nonneg T)
            (sq_pos_of_pos ht0) (by linarith))
        calc
          G t ≤ (T^2/t^2)*(F t+F (-t)) :=
            mul_le_mul_of_nonneg_right hk (add_nonneg (hFn t) (hFn (-t)))
          _ = _ := by ring)
    rw [integral_const_mul] at hm
    calc
      _ ≤ T^2*(4*A/(N*N)) := hm.trans (mul_le_mul_of_nonneg_left htail (sq_nonneg _))
      _ = _ := by ring
  rw [hGe, ← intervalIntegral.integral_interval_add_Ioi (a := 0) (b := N)
    hGi.integrableOn hGi.integrableOn,
    ← intervalIntegral.integral_add_adjacent_intervals
      (hGcont.intervalIntegrable 0 T) (hGcont.intervalIntegrable T N)]
  linarith

theorem mrt_dyadic_kernel_finite_height (b : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (hb : ∀ n ∈ Finset.Ioc N (2*N), ‖b n‖ ≤ 1)
    {T ε : ℝ} (hT : 0 < T) (hTN : T ≤ N) (hε : 0 ≤ ε)
    (hsmall : ∀ v, T ≤ v → v ≤ N →
      (∫ t in -v..v, ‖mrtDyadicPolynomial b N t‖^2) ≤ ε*(v/N+1)) :
    (∫ t : ℝ, mrtShortKernel T t * ‖mrtDyadicPolynomial b N t‖^2) ≤
      10*ε+64*Real.exp 1*(T/N)^2 := by
  let C : ℝ := (∑ n ∈ Finset.Ioc N (2*N), ‖b n‖*Real.exp (-Real.log (n:ℝ)))^2
  have he (t : ℝ) : mrtLogDirichlet (Finset.Ioc N (2*N)) b t =
      mrtDyadicPolynomial b N t :=
    mrt_log_dirichlet_polynomial _ (fun n hn =>
      lt_trans hN (Finset.mem_Ioc.mp hn).1) b t
  have hFc : Continuous (fun t => ‖mrtDyadicPolynomial b N t‖^2) :=
    (mrtExponentialPolynomial_continuous _ _ _).norm.pow 2
  have hbound (t : ℝ) : ‖mrtDyadicPolynomial b N t‖^2 ≤ C := by
    rw [← he]
    exact pow_le_pow_left₀ (norm_nonneg _) (mrt_log_dirichlet_norm _ _ t) 2
  have hm := mrt_short_kernel_finite_height _ hFc (fun _ => sq_nonneg _)
    hbound (by exact_mod_cast hN) hT hTN hε
    (by positivity : 0 ≤ 16*Real.exp 1) hsmall (fun v hv =>
      mrt_dyadic_mean_square b hN hb (lt_of_lt_of_le (by exact_mod_cast hN) hv))
  simpa only [show (4:ℝ)*(16*Real.exp 1) = 64*Real.exp 1 by ring] using hm

end TwoPointCorrelations

end OAI
