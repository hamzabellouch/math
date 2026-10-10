import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrimeProducts

namespace OAI

/-! High even moments of a prime Dirichlet polynomial.  Expanding the
power produces ordered prime tuples; unique factorization bounds each
coefficient fiber by the factorial, and the ordinary mean-square theorem
then applies to a polynomial of length `N ^ r`. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped BigOperators Classical

noncomputable def mrtPrimePowerCoefficient (P : Finset ℕ) (a : ℕ → ℂ)
    (r n : ℕ) : ℂ :=
  ∑ v ∈ (Fintype.piFinset fun _ : Fin r => P).filter
    (fun v => (∏ i, v i) = n), ∏ i, a (v i)

lemma mrt_prime_tuple_range (P : Finset ℕ) (N r : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hN : ∀ p ∈ P, p ≤ N)
    (v : Fin r → ℕ) (hv : v ∈ Fintype.piFinset fun _ : Fin r => P) :
    (∏ i, v i) ∈ Ioc 0 (N ^ r) := by
  have hm : ∀ i, v i ∈ P := Fintype.mem_piFinset.mp hv
  refine mem_Ioc.mpr ⟨prod_pos fun i _ => (hP _ (hm i)).pos, ?_⟩
  calc
    _ ≤ ∏ _i : Fin r, N := prod_le_prod fun i _ => hN _ (hm i)
    _ = _ := by simp

theorem mrt_prime_power_coefficient_mass (P : Finset ℕ) (a : ℕ → ℂ)
    (N r : ℕ) (hP : ∀ p ∈ P, p.Prime) (hN : ∀ p ∈ P, p ≤ N) :
    (∑ n ∈ Ioc 0 (N ^ r), ‖mrtPrimePowerCoefficient P a r n‖ ^ 2) ≤
      (r.factorial : ℝ) * (∑ p ∈ P, ‖a p‖ ^ 2) ^ r := by
  let S := Fintype.piFinset fun _ : Fin r => P
  have hs : ∀ v ∈ S, ∀ i, (v i).Prime := by
    intro v hv i
    exact hP _ (Fintype.mem_piFinset.mp hv i)
  calc
    _ ≤ ∑ n ∈ Ioc 0 (N ^ r), (r.factorial : ℝ) *
        ∑ v ∈ S.filter (fun v => (∏ i, v i) = n), ‖∏ i, a (v i)‖ ^ 2 := by
      apply sum_le_sum
      intro n _
      exact mrt_prime_product_coefficient_sq S hs (fun v => ∏ i, a (v i)) n
    _ = (r.factorial : ℝ) * ∑ v ∈ S, ‖∏ i, a (v i)‖ ^ 2 := by
      rw [← mul_sum]
      congr 1
      exact sum_fiberwise_of_maps_to (fun v hv => mrt_prime_tuple_range P N r hP hN v hv) _
    _ = _ := by
      congr 1
      simp only [norm_prod, ← prod_pow]
      exact (sum_pow' P (fun p => ‖a p‖ ^ 2) r).symm

lemma mrt_prime_tuple_phase {r : ℕ} (v : Fin r → ℕ)
    (hv : ∀ i, 0 < v i) (t : ℝ) :
    (∏ i, Complex.exp (((-Real.log (v i : ℝ) * t : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (((-Real.log ((∏ i, v i : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_sum]
  have hl : Real.log ((∏ i, v i : ℕ) : ℝ) = ∑ i, Real.log (v i : ℝ) := by
    push_cast
    exact Real.log_prod fun i _ => by exact_mod_cast (hv i).ne'
  rw [hl]
  congr 1
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_neg]
  rw [← sum_mul, ← sum_mul, sum_neg_distrib]

theorem mrt_prime_polynomial_power (P : Finset ℕ) (a : ℕ → ℂ)
    (N r : ℕ) (hP : ∀ p ∈ P, p.Prime) (hN : ∀ p ∈ P, p ≤ N) (t : ℝ) :
    (mrtExponentialPolynomial P a (fun p => -Real.log (p : ℝ)) t) ^ r =
      mrtExponentialPolynomial (Ioc 0 (N ^ r)) (mrtPrimePowerCoefficient P a r)
        (fun n => -Real.log (n : ℝ)) t := by
  unfold mrtExponentialPolynomial
  rw [sum_pow']
  symm
  calc
    _ = ∑ n ∈ Ioc 0 (N ^ r), ∑ v ∈ (Fintype.piFinset fun _ : Fin r => P).filter
        (fun v => (∏ i, v i) = n),
          (∏ i, a (v i)) * Complex.exp (((-Real.log (n : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
      apply sum_congr rfl
      intro n _
      exact sum_mul _ _ _
    _ = ∑ v ∈ Fintype.piFinset fun _ : Fin r => P,
        (∏ i, a (v i)) *
          Complex.exp (((-Real.log ((∏ i, v i : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
      calc
        _ = ∑ n ∈ Ioc 0 (N ^ r), ∑ v ∈ (Fintype.piFinset fun _ : Fin r => P).filter
            (fun v => (∏ i, v i) = n), (∏ i, a (v i)) *
              Complex.exp (((-Real.log ((∏ i, v i : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
          apply sum_congr rfl
          intro n _
          apply sum_congr rfl
          intro v hv
          rw [(mem_filter.mp hv).2]
        _ = _ := sum_fiberwise_of_maps_to
          (fun v hv => mrt_prime_tuple_range P N r hP hN v hv) _
    _ = _ := by
      apply sum_congr rfl
      intro v hv
      rw [prod_mul_distrib, mrt_prime_tuple_phase v
        (fun i => (hP _ (Fintype.mem_piFinset.mp hv i)).pos) t]

/-- The prime-polynomial high-moment bound with an absolute constant.
Repeated prime factors are included; their only cost is `r!`. -/
theorem mrt_prime_polynomial_moment (P : Finset ℕ) (a : ℕ → ℂ)
    (N r : ℕ) (hP : ∀ p ∈ P, p.Prime) (hN : ∀ p ∈ P, p ≤ N)
    {T : ℝ} (hT : 0 < T) :
    (∫ t in -T..T, ‖mrtExponentialPolynomial P a (fun p => -Real.log (p : ℝ)) t‖ ^
      (2 * r)) ≤
      8 * Real.exp 1 * (T + (N ^ r : ℕ)) *
        (r.factorial : ℝ) * (∑ p ∈ P, ‖a p‖ ^ 2) ^ r := by
  have he : (fun t => ‖mrtExponentialPolynomial P a
      (fun p => -Real.log (p : ℝ)) t‖ ^ (2 * r)) =
      fun t => ‖mrtExponentialPolynomial (Ioc 0 (N ^ r))
        (mrtPrimePowerCoefficient P a r) (fun n => -Real.log (n : ℝ)) t‖ ^ 2 := by
    funext t
    rw [← mrt_prime_polynomial_power P a N r hP hN t, norm_pow, ← pow_mul]
    rw [Nat.mul_comm]
  rw [he]
  apply (mrt_dirichlet_mean_square (N ^ r) (mrtPrimePowerCoefficient P a r) hT).trans
  calc
    _ ≤ (8 * Real.exp 1 * (T + (N ^ r : ℕ))) *
        ((r.factorial : ℝ) * (∑ p ∈ P, ‖a p‖ ^ 2) ^ r) := by
      apply mul_le_mul_of_nonneg_left (mrt_prime_power_coefficient_mass P a N r hP hN)
      positivity
    _ = _ := by ring

end TwoPointCorrelations

end OAI
