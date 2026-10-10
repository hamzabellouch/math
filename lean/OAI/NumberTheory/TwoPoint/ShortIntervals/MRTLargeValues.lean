import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSampling

namespace OAI

/-! Large values at one-separated heights, obtained from the exact
prime-product expansion and the finite sampling inequality. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrt_dirichlet_derivative_mass (N : ℕ) (a : ℕ → ℂ) :
    (∑ n ∈ Ioc 0 N, ‖a n * (((-Real.log (n : ℝ)) : ℂ) * Complex.I)‖ ^ 2) ≤
      (Real.log (N : ℝ)) ^ 2 * ∑ n ∈ Ioc 0 N, ‖a n‖ ^ 2 := by
  rw [mul_sum]
  apply sum_le_sum
  intro n hn
  have hn0 : 0 < n := (mem_Ioc.mp hn).1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Ioc.mp hn).2
  have hlog0 := Real.log_nonneg hn1
  have hlogN := Real.log_le_log (by positivity : (0 : ℝ) < n) hnN
  simp only [norm_mul, Complex.norm_I, mul_one, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hlog0, mul_pow]
  calc
    _ ≤ ‖a n‖ ^ 2 * (Real.log (N : ℝ)) ^ 2 := by gcongr
    _ = _ := mul_comm _ _

theorem mrt_dirichlet_separated_samples (N : ℕ) (a : ℕ → ℂ)
    (S : Finset ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hS : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial (Ioc 0 N) a
      (fun n => -Real.log (n : ℝ)) t‖ ^ 2) ≤
      8 * Real.exp 1 * (T + 1 + N) * (2 + (Real.log (N : ℝ)) ^ 2) *
        ∑ n ∈ Ioc 0 N, ‖a n‖ ^ 2 := by
  let q := mrtExponentialPolynomial (Ioc 0 N) a (fun n => -Real.log (n : ℝ))
  let q' := mrtExponentialPolynomial (Ioc 0 N)
    (fun n => a n * (((-Real.log (n : ℝ)) : ℂ) * Complex.I))
    (fun n => -Real.log (n : ℝ))
  have hq := mrtExponentialPolynomial_continuous (Ioc 0 N) a
    (fun n => -Real.log (n : ℝ))
  have hq' := mrtExponentialPolynomial_continuous (Ioc 0 N)
    (fun n => a n * (((-Real.log (n : ℝ)) : ℂ) * Complex.I))
    (fun n => -Real.log (n : ℝ))
  have hder (t : ℝ) : HasDerivAt q (q' t) t := by
    simpa only [q, q', Complex.ofReal_neg] using
      mrt_exponential_polynomial_deriv (Ioc 0 N) a (fun n => -Real.log (n : ℝ)) t
  have hs := mrt_separated_square_samples S q q' hq hq' hder hsep (-(T + 1)) (T + 1)
    (by linarith) (fun t ht => by
      have hh := abs_le.mp (hS t ht)
      constructor <;> linarith)
  have hm := mrt_dirichlet_mean_square N a (show 0 < T + 1 by linarith)
  have hm' := mrt_dirichlet_mean_square N
    (fun n => a n * (((-Real.log (n : ℝ)) : ℂ) * Complex.I))
    (show 0 < T + 1 by linarith)
  have hd := mrt_dirichlet_derivative_mass N a
  have hp : 0 ≤ 8 * Real.exp 1 * (T + 1 + N) := by positivity
  calc
    _ ≤ ∫ t in -(T + 1)..(T + 1), 2 * ‖q t‖ ^ 2 + ‖q' t‖ ^ 2 := hs
    _ = 2 * (∫ t in -(T + 1)..(T + 1), ‖q t‖ ^ 2) +
        ∫ t in -(T + 1)..(T + 1), ‖q' t‖ ^ 2 := by
      have hiq : IntervalIntegrable (fun t => 2 * ‖q t‖ ^ 2) volume (-(T + 1)) (T + 1) :=
        (continuous_const.mul (hq.norm.pow 2)).intervalIntegrable _ _
      have hiq' : IntervalIntegrable (fun t => ‖q' t‖ ^ 2) volume (-(T + 1)) (T + 1) :=
        (hq'.norm.pow 2).intervalIntegrable _ _
      rw [intervalIntegral.integral_add hiq hiq', intervalIntegral.integral_const_mul]
    _ ≤ 2 * (8 * Real.exp 1 * (T + 1 + N) * ∑ n ∈ Ioc 0 N, ‖a n‖ ^ 2) +
        8 * Real.exp 1 * (T + 1 + N) *
          ((Real.log (N : ℝ)) ^ 2 * ∑ n ∈ Ioc 0 N, ‖a n‖ ^ 2) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hm (by norm_num))
        (hm'.trans (mul_le_mul_of_nonneg_left hd hp))
    _ = _ := by ring

/-- The sampled `2r`-th moment of an actual prime Dirichlet polynomial.
The extra logarithmic square comes only from sampling the continuous
moment on unit intervals. -/
theorem mrt_prime_separated_moment (P : Finset ℕ) (a : ℕ → ℂ)
    (N r : ℕ) (hP : ∀ p ∈ P, p.Prime) (hN : ∀ p ∈ P, p ≤ N)
    (S : Finset ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hS : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) :
    (∑ t ∈ S, ‖mrtExponentialPolynomial P a (fun p => -Real.log (p : ℝ)) t‖ ^
      (2 * r)) ≤
      8 * Real.exp 1 * (T + 1 + (N ^ r : ℕ)) *
        (2 + (Real.log (N ^ r : ℕ)) ^ 2) *
        (r.factorial : ℝ) * (∑ p ∈ P, ‖a p‖ ^ 2) ^ r := by
  have he (t : ℝ) : ‖mrtExponentialPolynomial P a
      (fun p => -Real.log (p : ℝ)) t‖ ^ (2 * r) =
      ‖mrtExponentialPolynomial (Ioc 0 (N ^ r)) (mrtPrimePowerCoefficient P a r)
        (fun n => -Real.log (n : ℝ)) t‖ ^ 2 := by
    rw [← mrt_prime_polynomial_power P a N r hP hN t, norm_pow, ← pow_mul]
    rw [Nat.mul_comm]
  simp_rw [he]
  apply (mrt_dirichlet_separated_samples (N ^ r) (mrtPrimePowerCoefficient P a r)
    S hT hS hsep).trans
  calc
    _ ≤ (8 * Real.exp 1 * (T + 1 + (N ^ r : ℕ)) *
        (2 + (Real.log (N ^ r : ℕ)) ^ 2)) *
        ((r.factorial : ℝ) * (∑ p ∈ P, ‖a p‖ ^ 2) ^ r) := by
      apply mul_le_mul_of_nonneg_left (mrt_prime_power_coefficient_mass P a N r hP hN)
      positivity
    _ = _ := by ring

/-- A cardinality bound for one-separated large values. -/
theorem mrt_prime_large_values (P : Finset ℕ) (a : ℕ → ℂ)
    (N r : ℕ) (hP : ∀ p ∈ P, p.Prime) (hN : ∀ p ∈ P, p ≤ N)
    (S : Finset ℝ) {T V : ℝ} (hT : 0 ≤ T) (hV : 0 < V)
    (hS : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|)
    (hlarge : ∀ t ∈ S,
      V ≤ ‖mrtExponentialPolynomial P a (fun p => -Real.log (p : ℝ)) t‖) :
    (S.card : ℝ) ≤
      (8 * Real.exp 1 * (T + 1 + (N ^ r : ℕ)) *
        (2 + (Real.log (N ^ r : ℕ)) ^ 2) *
        (r.factorial : ℝ) * (∑ p ∈ P, ‖a p‖ ^ 2) ^ r) / V ^ (2 * r) := by
  apply (le_div_iff₀ (pow_pos hV _)).mpr
  calc
    _ = ∑ _t ∈ S, V ^ (2 * r) := by simp
    _ ≤ ∑ t ∈ S, ‖mrtExponentialPolynomial P a
        (fun p => -Real.log (p : ℝ)) t‖ ^ (2 * r) := by
      apply sum_le_sum
      intro t ht
      exact pow_le_pow_left₀ hV.le (hlarge t ht) _
    _ ≤ _ := mrt_prime_separated_moment P a N r hP hN S hT hS hsep

/-- A convenient geometric-decay form.  The hypothesis compares the
moment order times the coefficient square mass with the large-value
threshold, rather than hiding this numerical requirement in an input. -/
theorem mrt_prime_large_values_geometric (P : Finset ℕ) (a : ℕ → ℂ)
    (N r : ℕ) (hP : ∀ p ∈ P, p.Prime) (hN : ∀ p ∈ P, p ≤ N)
    (S : Finset ℝ) {T V ρ : ℝ} (hT : 0 ≤ T) (hV : 0 < V)
    (hmass : (r : ℝ) * (∑ p ∈ P, ‖a p‖ ^ 2) ≤ ρ * V ^ 2)
    (hS : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|)
    (hlarge : ∀ t ∈ S,
      V ≤ ‖mrtExponentialPolynomial P a (fun p => -Real.log (p : ℝ)) t‖) :
    (S.card : ℝ) ≤
      (8 * Real.exp 1 * (T + 1 + (N ^ r : ℕ)) *
        (2 + (Real.log (N ^ r : ℕ)) ^ 2)) * ρ ^ r := by
  have hf : (r.factorial : ℝ) ≤ (r : ℝ) ^ r := by
    exact_mod_cast Nat.factorial_le_pow r
  have hmass0 : 0 ≤ ∑ p ∈ P, ‖a p‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hpow : (r.factorial : ℝ) * (∑ p ∈ P, ‖a p‖ ^ 2) ^ r ≤
      ρ ^ r * V ^ (2 * r) := by
    calc
      _ ≤ (r : ℝ) ^ r * (∑ p ∈ P, ‖a p‖ ^ 2) ^ r :=
        mul_le_mul_of_nonneg_right hf (pow_nonneg hmass0 _)
      _ = ((r : ℝ) * (∑ p ∈ P, ‖a p‖ ^ 2)) ^ r := (mul_pow _ _ _).symm
      _ ≤ (ρ * V ^ 2) ^ r := pow_le_pow_left₀ (by positivity) hmass _
      _ = _ := by rw [mul_pow, ← pow_mul]
  have hconst : 0 ≤ 8 * Real.exp 1 * (T + 1 + (N ^ r : ℕ)) *
      (2 + (Real.log (N ^ r : ℕ)) ^ 2) := by positivity
  apply (mrt_prime_large_values P a N r hP hN S hT hV hS hsep hlarge).trans
  apply (div_le_iff₀ (pow_pos hV _)).mpr
  have hh := mul_le_mul_of_nonneg_left hpow hconst
  convert hh using 1 <;> ring

end TwoPointCorrelations

end OAI
