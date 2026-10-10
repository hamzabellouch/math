import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.DivisorMoment

/-- A nonnegative multiplicative function is bounded by its finite Euler product. -/
theorem sum_Icc_le_factorial_euler (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) (hpos : ∀ n, 0 ≤ f n) (T : ℕ) :
    (∑ n ∈ Finset.Icc 1 T, f n) ≤
      ∏ p ∈ T.factorial.primeFactors,
        ∑ j ∈ Finset.range (T.factorial.factorization p + 1), f (p ^ j) := by
  have hsub : Finset.Icc 1 T ⊆ T.factorial.divisors := by
    intro n hn
    obtain ⟨hnpos, hnT⟩ := Finset.mem_Icc.mp hn
    exact Nat.mem_divisors.mpr
      ⟨Nat.dvd_factorial hnpos hnT, Nat.factorial_ne_zero T⟩
  calc
    (∑ n ∈ Finset.Icc 1 T, f n) ≤ ∑ n ∈ T.factorial.divisors, f n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hpos n)
    _ = (f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) T.factorial :=
      ArithmeticFunction.coe_mul_zeta_apply.symm
    _ = ∏ p ∈ T.factorial.primeFactors,
        (f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ))
          (p ^ T.factorial.factorization p) := by
      rw [(hf.mul ArithmeticFunction.isMultiplicative_zeta.natCast).multiplicative_factorization
        _ (Nat.factorial_ne_zero T)]
      rfl
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [ArithmeticFunction.coe_mul_zeta_apply,
        Nat.sum_divisors_prime_pow (Nat.prime_of_mem_primeFactors hp)]

/-- An exponential local bound turns the finite Euler product into a prime sum. -/
theorem sum_Icc_le_exp_prime_sum (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) (hpos : ∀ n, 0 ≤ f n)
    (T : ℕ) (C : ℝ) (w : ℕ → ℝ)
    (hlocal : ∀ p, p.Prime → p ≤ T → ∀ L : ℕ,
      (∑ j ∈ Finset.range (L + 1), f (p ^ j)) ≤ Real.exp (C * w p)) :
    (∑ n ∈ Finset.Icc 1 T, f n) ≤
      Real.exp (C * ∑ p ∈ T.factorial.primeFactors, w p) := by
  apply (sum_Icc_le_factorial_euler f hf hpos T).trans
  rw [Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro p hp
    exact Finset.sum_nonneg (fun j _ => hpos (p ^ j))
  · intro p hp
    obtain ⟨hpprime, hpdvd, _⟩ := Nat.mem_primeFactors.mp hp
    exact hlocal p hpprime (hpprime.dvd_factorial.mp hpdvd) _

/-- The multiplicative weight used in harmonic and Rankin divisor moments. -/
def divisorMomentWeight (r : ℕ) (σ : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else (n.divisors.card : ℝ) ^ r * (n : ℝ) ^ (-σ), by simp⟩

theorem divisorMomentWeight_nonneg (r : ℕ) (σ : ℝ) (n : ℕ) :
    0 ≤ divisorMomentWeight r σ n := by
  unfold divisorMomentWeight
  simp only [ArithmeticFunction.coe_mk]
  split_ifs
  · rfl
  · positivity

theorem divisorMomentWeight_multiplicative (r : ℕ) (σ : ℝ) :
    (divisorMomentWeight r σ).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  constructor
  · simp [divisorMomentWeight]
  · intro m n hm hn hcop
    simp only [divisorMomentWeight, ArithmeticFunction.coe_mk, ite_eq_right hm, ite_eq_right hn,
      ite_eq_right (Nat.mul_ne_zero hm hn), hcop.card_divisors_mul, Nat.cast_mul, mul_pow,
      Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring

theorem divisorMomentWeight_prime_pow (r : ℕ) (σ : ℝ) {p : ℕ}
    (hp : p.Prime) (j : ℕ) :
    divisorMomentWeight r σ (p ^ j) = (j + 1 : ℝ) ^ r * ((p : ℝ) ^ (-σ)) ^ j := by
  have hcard : (p ^ j).divisors.card = j + 1 := by
    rw [← ArithmeticFunction.sigma_zero_apply,
      ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  simp only [divisorMomentWeight, ArithmeticFunction.coe_mk,
    ite_eq_right (pow_ne_zero j hp.ne_zero), hcard, Nat.cast_add, Nat.cast_one, Nat.cast_pow]
  rw [← Real.rpow_natCast_mul (Nat.cast_nonneg p), mul_comm (j : ℝ) (-σ),
    Real.rpow_mul_natCast (Nat.cast_nonneg p)]

/-- Divisor moments bounded by a truncated prime-power Euler product. -/
theorem divisor_moment_sum_le_euler (r T : ℕ) (σ : ℝ) :
    (∑ n ∈ Finset.Icc 1 T, (n.divisors.card : ℝ) ^ r * (n : ℝ) ^ (-σ)) ≤
      ∏ p ∈ T.factorial.primeFactors,
        ∑ j ∈ Finset.range (T.factorial.factorization p + 1),
          (j + 1 : ℝ) ^ r * ((p : ℝ) ^ (-σ)) ^ j := by
  have h := sum_Icc_le_factorial_euler (divisorMomentWeight r σ)
    (divisorMomentWeight_multiplicative r σ) (divisorMomentWeight_nonneg r σ) T
  convert h using 1
  · apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    simp [divisorMomentWeight, hn0]
  · apply Finset.prod_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro j hj
    exact (divisorMomentWeight_prime_pow r σ (Nat.prime_of_mem_primeFactors hp) j).symm

/-- Restriction to integers supported on a prescribed finite prime set. -/
def smoothRestriction (P : Finset ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n.primeFactors ⊆ P then f n else 0, by simp⟩

theorem smoothRestriction_multiplicative (P : Finset ℕ) (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) : (smoothRestriction P f).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  constructor
  · simp [smoothRestriction, hf.map_one]
  · intro m n hm hn hcop
    by_cases hmP : m.primeFactors ⊆ P <;> by_cases hnP : n.primeFactors ⊆ P <;>
      simp [smoothRestriction, Nat.primeFactors_mul hm hn, Finset.union_subset_iff,
        hmP, hnP, hf.map_mul_of_coprime hcop]

theorem smoothRestriction_nonneg (P : Finset ℕ) (f : ArithmeticFunction ℝ)
    (hpos : ∀ n, 0 ≤ f n) (n : ℕ) : 0 ≤ smoothRestriction P f n := by
  simp only [smoothRestriction, ArithmeticFunction.coe_mk]
  split_ifs
  · exact hpos n
  · rfl

theorem smoothRestriction_local (P : Finset ℕ) (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) {p : ℕ} (hp : p.Prime) (L : ℕ) :
    (∑ j ∈ Finset.range (L + 1), smoothRestriction P f (p ^ j)) =
      if p ∈ P then ∑ j ∈ Finset.range (L + 1), f (p ^ j) else 1 := by
  rw [Finset.sum_range_succ']
  by_cases hpP : p ∈ P
  · rw [ite_eq_left hpP, Finset.sum_range_succ']
    simp [smoothRestriction, Nat.primeFactors_pow, hp.primeFactors, hpP]
  · rw [ite_eq_right hpP]
    simp [smoothRestriction, Nat.primeFactors_pow, hp.primeFactors, hpP, hf.map_one]

/-- The same Euler bound restricted to smooth integers uses only their allowed primes. -/
theorem sum_smooth_le_factorial_euler (P : Finset ℕ) (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) (hpos : ∀ n, 0 ≤ f n) (T : ℕ) :
    (∑ n ∈ (Finset.Icc 1 T).filter (fun n => n.primeFactors ⊆ P), f n) ≤
      ∏ p ∈ T.factorial.primeFactors ∩ P,
        ∑ j ∈ Finset.range (T.factorial.factorization p + 1), f (p ^ j) := by
  have h := sum_Icc_le_factorial_euler (smoothRestriction P f)
    (smoothRestriction_multiplicative P f hf) (smoothRestriction_nonneg P f hpos) T
  rw [← Finset.prod_ite_mem] 
  convert h using 1
  · simp only [Finset.sum_filter, smoothRestriction, ArithmeticFunction.coe_mk]
  · apply Finset.prod_congr rfl
    intro p hp
    exact (smoothRestriction_local P f hf (Nat.prime_of_mem_primeFactors hp) _).symm

/-- Exponential version of the smooth Euler bound. -/
theorem sum_smooth_le_exp_prime_sum (P : Finset ℕ) (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) (hpos : ∀ n, 0 ≤ f n)
    (T : ℕ) (C : ℝ) (w : ℕ → ℝ)
    (hlocal : ∀ p, p.Prime → p ≤ T → p ∈ P → ∀ L : ℕ,
      (∑ j ∈ Finset.range (L + 1), f (p ^ j)) ≤ Real.exp (C * w p)) :
    (∑ n ∈ (Finset.Icc 1 T).filter (fun n => n.primeFactors ⊆ P), f n) ≤
      Real.exp (C * ∑ p ∈ T.factorial.primeFactors ∩ P, w p) := by
  apply (sum_smooth_le_factorial_euler P f hf hpos T).trans
  rw [Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro p hp
    exact Finset.sum_nonneg (fun j _ => hpos (p ^ j))
  · intro p hp
    obtain ⟨hpFac, hpP⟩ := Finset.mem_inter.mp hp
    obtain ⟨hpprime, hpdvd, _⟩ := Nat.mem_primeFactors.mp hpFac
    exact hlocal p hpprime (hpprime.dvd_factorial.mp hpdvd) hpP _

theorem local_divisor_sum_pos (r L : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 < ∑ j ∈ Finset.range (L + 1), (j + 1 : ℝ) ^ r * x ^ j := by
  have h := Finset.single_le_sum
    (s := Finset.range (L + 1)) (f := fun j : ℕ => (j + 1 : ℝ) ^ r * x ^ j)
    (fun j _ => by positivity) (show 0 ∈ Finset.range (L + 1) by simp)
  simp only [Nat.cast_zero, zero_add, one_pow, pow_zero, mul_one] at h
  linarith

/-- A uniform logarithmic local-factor bound controls the harmonic divisor sum. -/
theorem divisor_moment_sum_le_exp (r T : ℕ) (σ C : ℝ)
    (hlocal : ∀ p, p.Prime → p ≤ T → ∀ L : ℕ,
      Real.log (∑ j ∈ Finset.range (L + 1),
        (j + 1 : ℝ) ^ r * ((p : ℝ) ^ (-σ)) ^ j) ≤ C * (p : ℝ) ^ (-σ)) :
    (∑ n ∈ Finset.Icc 1 T, (n.divisors.card : ℝ) ^ r * (n : ℝ) ^ (-σ)) ≤
      Real.exp (C * ∑ p ∈ T.factorial.primeFactors, (p : ℝ) ^ (-σ)) := by
  have h := sum_Icc_le_exp_prime_sum (divisorMomentWeight r σ)
    (divisorMomentWeight_multiplicative r σ) (divisorMomentWeight_nonneg r σ)
    T C (fun p => (p : ℝ) ^ (-σ)) (by
      intro p hp hpT L
      simp_rw [divisorMomentWeight_prime_pow r σ hp]
      have hpos := local_divisor_sum_pos r L ((p : ℝ) ^ (-σ)) (by positivity)
      calc
        _ = Real.exp (Real.log _) := (Real.exp_log hpos).symm
        _ ≤ _ := Real.exp_le_exp.mpr (hlocal p hp hpT L))
  convert h using 1
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  simp [divisorMomentWeight, hn0]

/-- Smooth analogue, used after the Rankin weight is inserted. -/
theorem smooth_divisor_moment_sum_le_exp (P : Finset ℕ) (r T : ℕ) (σ C : ℝ)
    (hlocal : ∀ p, p.Prime → p ≤ T → p ∈ P → ∀ L : ℕ,
      Real.log (∑ j ∈ Finset.range (L + 1),
        (j + 1 : ℝ) ^ r * ((p : ℝ) ^ (-σ)) ^ j) ≤ C * (p : ℝ) ^ (-σ)) :
    (∑ n ∈ (Finset.Icc 1 T).filter (fun n => n.primeFactors ⊆ P),
      (n.divisors.card : ℝ) ^ r * (n : ℝ) ^ (-σ)) ≤
      Real.exp (C * ∑ p ∈ T.factorial.primeFactors ∩ P, (p : ℝ) ^ (-σ)) := by
  have h := sum_smooth_le_exp_prime_sum P (divisorMomentWeight r σ)
    (divisorMomentWeight_multiplicative r σ) (divisorMomentWeight_nonneg r σ)
    T C (fun p => (p : ℝ) ^ (-σ)) (by
      intro p hp hpT hpP L
      simp_rw [divisorMomentWeight_prime_pow r σ hp]
      have hpos := local_divisor_sum_pos r L ((p : ℝ) ^ (-σ)) (by positivity)
      calc
        _ = Real.exp (Real.log _) := (Real.exp_log hpos).symm
        _ ≤ _ := Real.exp_le_exp.mpr (hlocal p hp hpT hpP L))
  convert h using 1
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1; omega
  simp [divisorMomentWeight, hn0]

end Problem337.DivisorMoment

end

end OAI
