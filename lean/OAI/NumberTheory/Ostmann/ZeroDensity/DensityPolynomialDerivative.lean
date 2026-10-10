import OAI.NumberTheory.Ostmann.ZeroDensity.DensitySeparatedSampling

namespace OAI

/-! # The explicit height derivative and its coefficient energy -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def densityDerivativeCoeff (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (-2 * (Real.pi : ℂ) * Complex.I * (Real.log n : ℂ)) * a n

 theorem density_log_phase_derivative (l t : ℝ) :
    HasDerivAt (fun x : ℝ => realAdditivePhase (-(l * x)))
      ((-2 * (Real.pi : ℂ) * Complex.I * (l : ℂ)) * realAdditivePhase (-(l * t))) t := by
  let k : ℂ := -2 * (Real.pi : ℂ) * Complex.I * (l : ℂ)
  have he (x : ℝ) : realAdditivePhase (-(l * x)) = Complex.exp (k * (x : ℂ)) := by
    unfold realAdditivePhase
    congr 1
    dsimp [k]
    push_cast
    ring
  have hd := (((hasDerivAt_id t).ofReal_comp).const_mul k).cexp
  simp only [id_eq, Complex.ofReal_one, mul_one] at hd
  convert hd using 1
  · funext x
    exact he x
  · rw [he]
    change k * Complex.exp (k * (t : ℂ)) = Complex.exp (k * (t : ℂ)) * k
    ring

 theorem density_polynomial_hasDerivAt (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => ∑ n ∈ S, a n * realAdditivePhase (-(Real.log n * x)))
      (∑ n ∈ S, densityDerivativeCoeff a n * realAdditivePhase (-(Real.log n * t))) t := by
  convert HasDerivAt.fun_sum (u := S) (fun n _ =>
    (density_log_phase_derivative (Real.log n) t).const_mul (a n)) using 1
  apply Finset.sum_congr rfl
  intro n _
  unfold densityDerivativeCoeff
  ring

 theorem density_polynomial_continuous (S : Finset ℕ) (a : ℕ → ℂ) :
    Continuous (fun t : ℝ => ∑ n ∈ S, a n * realAdditivePhase (-(Real.log n * t))) :=
  continuous_iff_continuousAt.mpr (fun t => (density_polynomial_hasDerivAt S a t).continuousAt)

 theorem density_derivative_coefficient_bound (N : ℕ) (a : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 N, ‖densityDerivativeCoeff a n‖ ^ 2) ≤
      64 * (Real.log (N + 1 : ℕ)) ^ 2 * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hnR
  have hlogN : Real.log n ≤ Real.log (N + 1 : ℕ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (by omega : n ≤ N + 1))
  have hcoef : ‖-2 * (Real.pi : ℂ) * Complex.I * (Real.log n : ℂ)‖ ≤
      8 * Real.log (N + 1 : ℕ) := by
    simp only [norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_I, mul_one, abs_of_pos Real.pi_pos,
      abs_of_nonneg hlog]
    nlinarith [Real.pi_lt_four, Real.pi_pos]
  rw [densityDerivativeCoeff, norm_mul, mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  nlinarith [norm_nonneg (-2 * (Real.pi : ℂ) * Complex.I * (Real.log n : ℂ))]

end Ostmann

end OAI
