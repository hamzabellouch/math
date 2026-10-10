import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTKernelTail

namespace OAI

/-! A finite-height kernel bound measured at the natural short-window
frequency scale. It preserves the linear first-prime-band cost. -/

namespace TwoPointCorrelations

open MeasureTheory Set

theorem mrt_short_kernel_linear_height (F : ℝ → ℝ) (hF : Continuous F)
    (hFn : ∀ t, 0 ≤ F t) {C N T ε A : ℝ} (hC : ∀ t, F t ≤ C)
    (hN : 0 < N) (hT : 0 < T) (hTN : T ≤ N) (hε : 0 ≤ ε) (hA : 0 ≤ A)
    (hsmall : ∀ v, T ≤ v → v ≤ N →
      (∫ t in -v..v, F t) ≤ ε*(v/T+1))
    (hglobal : ∀ v, N ≤ v → (∫ t in -v..v, F t) ≤ A*(v/N+1)) :
    (∫ t : ℝ, mrtShortKernel T t * F t) ≤ 6*ε+4*A*(T/N)^2 := by
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
    rw [div_self hT.ne']
    ring_nf
    exact le_rfl
  have hmid : (∫ t in T..N, G t) ≤ 4*ε := by
    have hratio := mrt_frequency_tail_finite F hF hFn hT le_rfl hTN hε hsmall
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
    calc
      _ ≤ T^2*(4*ε/(T*T)) := hm.trans
        (mul_le_mul_of_nonneg_left hratio (sq_nonneg _))
      _ = _ := by field_simp
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

lemma mrt_linear_prefix_two_slopes {N T Q v A B : ℝ}
    (hN : 0 < N) (hT : 0 < T) (hTN : T ≤ N) (hQ : 0 ≤ Q)
    (hv : 0 ≤ v) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    A*(v/N+1)+B*(v*Q/N+1) ≤
      (A+B*(1+T*Q/N))*(v/T+1) := by
  have hdiv : v/N ≤ v/T := div_le_div_of_nonneg_left hv hT hTN
  have he : (1+T*Q/N)*(v/T+1)-(v*Q/N+1) = v/T+T*Q/N := by
    field_simp
    ring
  have hlin : v*Q/N+1 ≤ (1+T*Q/N)*(v/T+1) := by
    have hn : 0 ≤ v/T+T*Q/N := by positivity
    linarith
  calc
    _ ≤ A*(v/T+1)+B*((1+T*Q/N)*(v/T+1)) :=
      add_le_add (mul_le_mul_of_nonneg_left (by linarith) hA)
        (mul_le_mul_of_nonneg_left hlin hB)
    _ = _ := by ring

theorem mrt_dyadic_kernel_linear_height (b : ℕ → ℂ) {N : ℕ} (hN : 0 < N)
    (hb : ∀ n ∈ Finset.Ioc N (2*N), ‖b n‖ ≤ 1)
    {T ε : ℝ} (hT : 0 < T) (hTN : T ≤ N) (hε : 0 ≤ ε)
    (hsmall : ∀ v, T ≤ v → v ≤ N →
      (∫ t in -v..v, ‖mrtDyadicPolynomial b N t‖^2) ≤ ε*(v/T+1)) :
    (∫ t : ℝ, mrtShortKernel T t * ‖mrtDyadicPolynomial b N t‖^2) ≤
      6*ε+64*Real.exp 1*(T/N)^2 := by
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
  have hm := mrt_short_kernel_linear_height _ hFc (fun _ => sq_nonneg _)
    hbound (by exact_mod_cast hN) hT hTN hε
    (by positivity : 0 ≤ 16*Real.exp 1) hsmall (fun v hv =>
      mrt_dyadic_mean_square b hN hb (lt_of_lt_of_le (by exact_mod_cast hN) hv))
  simpa only [show (4:ℝ)*(16*Real.exp 1) = 64*Real.exp 1 by ring] using hm


end TwoPointCorrelations

end OAI
