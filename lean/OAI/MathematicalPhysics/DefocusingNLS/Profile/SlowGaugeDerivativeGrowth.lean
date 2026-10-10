import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowGaugeGrowth

namespace OAI

/-! A polynomial envelope for the derivative, retaining the exponential gauge. -/

namespace DefocusingNLS

theorem gaugedSlowSolution_derivative_polynomial_envelope (q : ℂ) (M : ℕ)
    (hq : -1 < q.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℂ, 0 ≤ x.re → 1 ≤ ‖x‖ →
      ‖deriv (gaugedSlowSolution q M) x‖ ≤
        C*Real.exp (-x.re/2)*
          ‖x‖^((M : ℝ)/2+max (-q.re) 0+max (-(q+1).re) 0) := by
  obtain ⟨A,hA,hH⟩ := regularizedSlowSolution_polynomial_bound q (M+1) hq
  obtain ⟨B,hB,hD⟩ := iteratedDeriv_regularizedSlowSolution_polynomial_bound 1 q (M+1) hq
  refine ⟨B+((M : ℝ)+1)*A,by positivity,?_⟩
  intro x hx hn
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (zero_lt_one.trans_le hn).ne'
  have hM : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  have hfac : ‖(M : ℂ)/(2*x)-1/2‖ ≤ (M : ℝ)+1 := by
    calc
      _ ≤ ‖(M : ℂ)/(2*x)‖+‖(1/2 : ℂ)‖ := norm_sub_le _ _
      _ = (M : ℝ)/(2*‖x‖)+1/2 := by norm_num [norm_div,norm_mul]
      _ ≤ (M : ℝ)+1 := by
        have hh : (M : ℝ)/(2*‖x‖) ≤ (M : ℝ)/2 := by
          apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
          nlinarith
        linarith
  have hp₀ : ‖x‖^(max (-q.re) 0) ≤ ‖x‖^(max (-q.re) 0+max (-(q+1).re) 0) :=
    Real.rpow_le_rpow_of_exponent_le hn (by linarith [le_max_right (-(q+1).re) 0])
  have hp₁ : ‖x‖^(max (-(q+1).re) 0) ≤ ‖x‖^(max (-q.re) 0+max (-(q+1).re) 0) :=
    Real.rpow_le_rpow_of_exponent_le hn (by linarith [le_max_right (-q.re) 0])
  have hH' : ‖regularizedSlowSolution q (M+1) x‖ ≤
      A*‖x‖^(max (-q.re) 0+max (-(q+1).re) 0) :=
    (hH x hx hn).trans (mul_le_mul_of_nonneg_left hp₀ hA)
  have hD' : ‖deriv (regularizedSlowSolution q (M+1)) x‖ ≤
      B*‖x‖^(max (-q.re) 0+max (-(q+1).re) 0) := by
    have hd := hD x hx hn
    norm_num only [iteratedDeriv_one,Nat.cast_one] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left hp₁ hB)
  rw [(hasDerivAt_gaugedSlowSolution q M x hq hx hx0).deriv,norm_mul,slowGauge_norm]
  calc
    _ ≤ (Real.exp (-x.re/2)*‖x‖^((M : ℝ)/2))*
        ((B+((M : ℝ)+1)*A)*‖x‖^(max (-q.re) 0+max (-(q+1).re) 0)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        _ ≤ ‖deriv (regularizedSlowSolution q (M+1)) x‖+
            ‖(M : ℂ)/(2*x)-1/2‖*‖regularizedSlowSolution q (M+1) x‖ := by
          simpa only [norm_mul] using norm_add_le
            (deriv (regularizedSlowSolution q (M+1)) x)
            (((M : ℂ)/(2*x)-1/2)*regularizedSlowSolution q (M+1) x)
        _ ≤ B*‖x‖^(max (-q.re) 0+max (-(q+1).re) 0)+
            ((M : ℝ)+1)*(A*‖x‖^(max (-q.re) 0+max (-(q+1).re) 0)) :=
          add_le_add hD' (mul_le_mul hfac hH' (norm_nonneg _) (by positivity))
        _ = _ := by ring
    _ = _ := by
      simp only [Real.rpow_add (by linarith : 0 < ‖x‖)]
      ring

end DefocusingNLS

end OAI
