import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothPrincipalPartialSummation

namespace OAI

/-! # Quantitative PNT for the fixed smooth principal test

Only the classical quantitative Chebyshev estimate is used here. The
smoothing bounds are proved for the concrete test retained in the main proof.
-/

namespace Ostmann

open Filter MeasureTheory
open scoped BigOperators Interval

theorem smoothPrincipalError_rough_bound (D X : ℝ) (hD : 0 ≤ D) (hX : 0 < X)
    (hd : ∀ t : ℝ, |deriv primeMeanTest t| ≤ D) :
    smoothPrincipalError X ≤ D * (Real.log 4 + 5) * X := by
  rw [smoothPrincipalError_integral X hX]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := X) (C := D * (Real.log 4 + 5))
    (f := fun t : ℝ => deriv primeMeanTest (t / X) / X * (Chebyshev.psi t - t))
    (fun t ht => ?_)
  · simpa only [Real.norm_eq_abs, sub_zero, abs_of_pos hX] using hi
  rw [Set.uIoc_of_le hX.le] at ht
  have ht0 : 0 ≤ t := ht.1.le
  have hpsi : |Chebyshev.psi t - t| ≤ (Real.log 4 + 5) * t := by
    have hh := abs_sub_le (Chebyshev.psi t) 0 t
    simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg (Chebyshev.psi_nonneg t),
      abs_of_nonneg ht0] at hh
    linarith [Chebyshev.psi_le_const_mul_self ht0]
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hX]
  calc
    _ ≤ D / X * ((Real.log 4 + 5) * t) :=
      mul_le_mul (div_le_div_of_nonneg_right (hd _) hX.le) hpsi (abs_nonneg _)
        (div_nonneg hD hX.le)
    _ ≤ D / X * ((Real.log 4 + 5) * X) := by
      gcongr
      exact ht.2
    _ = _ := by field_simp

theorem smoothPrincipalError_of_psi_bound (C c D x0 X : ℝ)
    (hC : 0 ≤ C) (hc : 0 < c) (hD : 0 ≤ D)
    (hd : ∀ t : ℝ, |deriv primeMeanTest t| ≤ D)
    (hpsi : ∀ t : ℝ, x0 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t * Real.exp (-c * Real.sqrt (Real.log t)))
    (hX : 4 ≤ X) (hx0 : 2 * x0 ≤ X) :
    smoothPrincipalError X ≤ C * D * X *
      Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by
  have hX0 : 0 < X := by linarith
  rw [smoothPrincipalError_integral X hX0]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := X)
    (C := C * D * Real.exp (-(c / 2) * Real.sqrt (Real.log X)))
    (f := fun t : ℝ => deriv primeMeanTest (t / X) / X * (Chebyshev.psi t - t))
    (fun t ht => ?_)
  · have hh : |X - 0| = X := by simpa using abs_of_pos hX0
    rw [hh, Real.norm_eq_abs] at hi
    calc
      _ ≤ C * D * Real.exp (-(c / 2) * Real.sqrt (Real.log X)) * X := hi
      _ = _ := by ring
  rw [Set.uIoc_of_le hX0.le] at ht
  by_cases hsmall : t < X / 2
  · have hz : deriv primeMeanTest (t / X) = 0 := by
      apply primeMeanTest_deriv_zero_outside
      intro hmem
      have hh := (le_div_iff₀ hX0).mp hmem.1
      linarith
    rw [hz, zero_div, zero_mul, norm_zero]
    positivity
  have ht0 : 0 < t := ht.1
  have htlo : X / 2 ≤ t := le_of_not_gt hsmall
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hloglarge : 2 * Real.log 2 ≤ Real.log X := by
    rw [← hlog4]
    exact Real.log_le_log (by norm_num) hX
  have hlogt : Real.log X - Real.log 2 ≤ Real.log t := by
    have h := Real.log_le_log (show 0 < X / 2 by positivity) htlo
    rwa [Real.log_div hX0.ne' (by norm_num : (2 : ℝ) ≠ 0)] at h
  have hsqrt : Real.sqrt (Real.log X) / 2 ≤ Real.sqrt (Real.log t) := by
    calc
      _ = Real.sqrt (Real.log X / 4) := by rw [Real.sqrt_div hlogX]; norm_num
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
  have hexp : Real.exp (-c * Real.sqrt (Real.log t)) ≤
      Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have herr : |Chebyshev.psi t - t| ≤
      C * X * Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by
    calc
      _ ≤ C * t * Real.exp (-c * Real.sqrt (Real.log t)) :=
        hpsi t (by linarith)
      _ ≤ _ := by gcongr; exact ht.2
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hX0]
  calc
    _ ≤ D / X * (C * X * Real.exp (-(c / 2) * Real.sqrt (Real.log X))) :=
      mul_le_mul (div_le_div_of_nonneg_right (hd _) hX0.le) herr (abs_nonneg _)
        (div_nonneg hD hX0.le)
    _ = _ := by field_simp

/-- The fixed-test PNT follows from the classical quantitative Chebyshev PNT. -/
theorem publishedSmoothPrincipalPNT_of_chebyshev
    (hPNT : ∃ c > 0,
      (Chebyshev.psi - id) =O[atTop]
        (fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2)))) :
    PublishedSmoothPrincipalPNT := by
  obtain ⟨c, hc, hp⟩ := hPNT
  obtain ⟨C, hC, hbound⟩ := hp.exists_pos
  obtain ⟨x0, hx0⟩ := eventually_atTop.mp hbound.bound
  obtain ⟨D, hD, hd⟩ := primeMeanTest_deriv_bound
  let x1 := max x0 2
  have hpsi : ∀ t : ℝ, x1 ≤ t →
      |Chebyshev.psi t - t| ≤ C * t * Real.exp (-c * Real.sqrt (Real.log t)) := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans (by dsimp only [x1]; positivity) ht
    have hh := hx0 t ((le_max_left _ _).trans ht)
    simpa only [Pi.sub_apply, id_eq, Real.norm_eq_abs, Real.sqrt_eq_rpow,
      abs_of_nonneg (mul_nonneg ht0 (Real.exp_nonneg _)), mul_assoc] using hh
  let T : ℝ := max 4 (2 * x1)
  let K0 : ℝ := D * (Real.log 4 + 5)
  let K : ℝ := max (C * D)
    (K0 * Real.exp ((c / 2) * Real.sqrt (Real.log T))) + 1
  have hK0 : 0 ≤ K0 := by dsimp only [K0]; positivity
  have hK : 0 < K := by
    dsimp only [K]
    have hh : 0 ≤ C * D := mul_nonneg hC.le hD.le
    linarith [le_max_left (C * D) (K0 * Real.exp ((c / 2) * Real.sqrt (Real.log T)))]
  refine ⟨K, c / 2, hK, by linarith, ?_⟩
  intro X hX
  have hX0 : 0 < X := by linarith
  by_cases hTX : T ≤ X
  · have hh := smoothPrincipalError_of_psi_bound C c D x1 X hC.le hc hD.le hd hpsi
      ((le_max_left _ _).trans hTX) ((le_max_right _ _).trans hTX)
    refine hh.trans ?_
    have hCK : C * D ≤ K := by
      dsimp only [K]
      have hm := le_max_left (C * D) (K0 * Real.exp ((c / 2) * Real.sqrt (Real.log T)))
      linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCK hX0.le)
      (Real.exp_nonneg _)
  · have hXT : X ≤ T := le_of_not_ge hTX
    have hsqrt : Real.sqrt (Real.log X) ≤ Real.sqrt (Real.log T) :=
      Real.sqrt_le_sqrt (Real.log_le_log hX0 hXT)
    have hscale : K0 * Real.exp ((c / 2) * Real.sqrt (Real.log X)) ≤ K := by
      calc
        _ ≤ K0 * Real.exp ((c / 2) * Real.sqrt (Real.log T)) := by gcongr
        _ ≤ _ := by
          dsimp only [K]
          have hm := le_max_right (C * D) (K0 * Real.exp ((c / 2) * Real.sqrt (Real.log T)))
          linarith
    have hsmall : K0 ≤ K * Real.exp (-(c / 2) * Real.sqrt (Real.log X)) := by
      have hh := mul_le_mul_of_nonneg_right hscale
        (Real.exp_nonneg (-(c / 2) * Real.sqrt (Real.log X)))
      have he : (c / 2) * Real.sqrt (Real.log X) +
          -(c / 2) * Real.sqrt (Real.log X) = 0 := by ring
      simpa only [mul_assoc, ← Real.exp_add, he, Real.exp_zero, mul_one] using hh
    calc
      _ ≤ K0 * X := smoothPrincipalError_rough_bound D X hD.le hX0 hd
      _ ≤ (K * Real.exp (-(c / 2) * Real.sqrt (Real.log X))) * X :=
        mul_le_mul_of_nonneg_right hsmall hX0.le
      _ = _ := by ring

end Ostmann

end OAI
