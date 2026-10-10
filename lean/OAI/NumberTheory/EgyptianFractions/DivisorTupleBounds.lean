import Mathlib

namespace OAI
/-!
# Elementary summatory bounds for divisor tuples

These finite hyperbola estimates supply logarithmic remainder bounds for
square sieves.  They do not use a prime number theorem.
-/
noncomputable section
open scoped BigOperators
open Finset

namespace Problem337.SelbergError

/-- Ordered positive factor tuples, expressed by Dirichlet powers of zeta. -/
def divisorTupleCount (k n : ℕ) : ℕ :=
  (ArithmeticFunction.zeta ^ k) n

private lemma sum_divisorsAntidiagonal_le_rectangle (N : ℕ)
    (F : ℕ × ℕ → ℝ) (hF : ∀ x, 0 ≤ F x) :
    (∑ n ∈ Icc 1 N, ∑ x ∈ n.divisorsAntidiagonal, F x) ≤
      ∑ x ∈ Icc 1 N ×ˢ Icc 1 N, F x := by
  have hdisj : Set.PairwiseDisjoint (Icc 1 N : Finset ℕ)
      Nat.divisorsAntidiagonal := by
    intro n hn m hm hnm
    apply disjoint_left.mpr
    intro x hxn hxm
    exact hnm ((Nat.mem_divisorsAntidiagonal.mp hxn).1.symm.trans
      (Nat.mem_divisorsAntidiagonal.mp hxm).1)
  rw [← sum_biUnion hdisj]
  apply sum_le_sum_of_subset_of_nonneg
  · intro x hx
    obtain ⟨n, hn, hxn⟩ := mem_biUnion.mp hx
    obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hxn
    have ha : 0 < x.1 := by
      by_contra h
      have : x.1 = 0 := by omega
      simp [this] at hprod
      omega
    have hb : 0 < x.2 := by
      by_contra h
      have : x.2 = 0 := by omega
      simp [this] at hprod
      omega
    have haN : x.1 ≤ N := (Nat.le_of_dvd (by omega : 0 < n)
      ⟨x.2, hprod.symm⟩).trans (mem_Icc.mp hn).2
    have hbN : x.2 ≤ N := (Nat.le_of_dvd (by omega : 0 < n)
      ⟨x.1, by simpa [Nat.mul_comm] using hprod.symm⟩).trans (mem_Icc.mp hn).2
    exact mem_product.mpr ⟨mem_Icc.mpr ⟨ha, haN⟩, mem_Icc.mpr ⟨hb, hbN⟩⟩
  · intro x hx hxnot
    exact hF x

/-- The harmonic norm on an initial interval is submultiplicative for
Dirichlet convolution of nonnegative arithmetic functions. -/
theorem harmonic_convolution_le (f g : ArithmeticFunction ℕ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ((f * g) n : ℝ) / n) ≤
      (∑ a ∈ Icc 1 N, (f a : ℝ) / a) *
      (∑ b ∈ Icc 1 N, (g b : ℝ) / b) := by
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ x ∈ n.divisorsAntidiagonal,
        ((f x.1 : ℝ) / x.1) * ((g x.2 : ℝ) / x.2) := by
      apply sum_congr rfl
      intro n hn
      rw [ArithmeticFunction.mul_apply, Nat.cast_sum, sum_div]
      apply sum_congr rfl
      intro x hx
      have hp := (Nat.mem_divisorsAntidiagonal.mp hx).1
      rw [Nat.cast_mul, ← hp, Nat.cast_mul]
      ring
    _ ≤ ∑ x ∈ Icc 1 N ×ˢ Icc 1 N,
        ((f x.1 : ℝ) / x.1) * ((g x.2 : ℝ) / x.2) :=
      sum_divisorsAntidiagonal_le_rectangle N _ (by intro x; positivity)
    _ = _ := by rw [sum_product, sum_mul_sum]

lemma zeta_harmonic_sum (N : ℕ) :
    (∑ n ∈ Icc 1 N, (ArithmeticFunction.zeta n : ℝ) / n) =
      (harmonic N : ℝ) := by
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  apply sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
  simp [ArithmeticFunction.zeta_apply_ne hn0]

/-- The harmonic sum over ordered `k`-factor tuples has at most the expected
`k` logarithmic factors. -/
theorem divisorTuple_harmonic_le (k N : ℕ) :
    (∑ n ∈ Icc 1 N, (divisorTupleCount k n : ℝ) / n) ≤
      (harmonic N : ℝ) ^ k := by
  induction k with
  | zero =>
    simp only [divisorTupleCount, pow_zero, ArithmeticFunction.one_apply]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_div, zero_div]
    by_cases hN : 1 ≤ N
    · simp [hN]
    · have : N = 0 := by omega
      simp [this]
  | succ k ih =>
    have h := harmonic_convolution_le (ArithmeticFunction.zeta ^ k)
      ArithmeticFunction.zeta N
    rw [zeta_harmonic_sum] at h
    calc
      _ ≤ (∑ n ∈ Icc 1 N, (divisorTupleCount k n : ℝ) / n) *
          (harmonic N : ℝ) := by simpa [divisorTupleCount, pow_succ] using h
      _ ≤ (harmonic N : ℝ) ^ k * (harmonic N : ℝ) :=
        mul_le_mul_of_nonneg_right ih (by rw [harmonic, Rat.cast_sum]; positivity)
      _ = _ := (pow_succ _ _).symm

/-- A uniform summatory bound, with one harmless extra logarithmic factor.
It holds also at `N = 0` and requires no squarefreeness restriction. -/
theorem divisorTuple_sum_le (k N : ℕ) :
    (∑ n ∈ Icc 1 N, (divisorTupleCount k n : ℝ)) ≤
      (N : ℝ) * (harmonic N : ℝ) ^ k := by
  calc
    _ ≤ ∑ n ∈ Icc 1 N, (N : ℝ) * ((divisorTupleCount k n : ℝ) / n) := by
      apply sum_le_sum
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
      rw [← mul_div_assoc, le_div_iff₀ hn0]
      nlinarith [show (0 : ℝ) ≤ divisorTupleCount k n by positivity]
    _ = (N : ℝ) * ∑ n ∈ Icc 1 N, (divisorTupleCount k n : ℝ) / n :=
      (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (divisorTuple_harmonic_le k N) (by positivity)

/-- At a prime, there are exactly `k` ordered `k`-factor tuples. -/
theorem divisorTupleCount_prime (k p : ℕ) (hp : p.Prime) :
    divisorTupleCount k p = k := by
  induction k with
  | zero => simp [divisorTupleCount, hp.ne_one]
  | succ k ih =>
    have h1 : (ArithmeticFunction.zeta ^ k) 1 = 1 :=
      ArithmeticFunction.isMultiplicative_zeta.pow.1
    change (ArithmeticFunction.zeta ^ (k + 1)) p = k + 1
    rw [pow_succ, ArithmeticFunction.mul_zeta_apply, hp.divisors]
    change (ArithmeticFunction.zeta ^ k) p = k at ih
    simp [hp.ne_one.symm, h1, ih, Nat.add_comm]

/-- A squarefree number has one independent choice among `k` tuple positions
for every prime factor. -/
theorem divisorTupleCount_squarefree (k n : ℕ) (hn : Squarefree n) :
    divisorTupleCount k n = k ^ n.primeFactors.card := by
  have hmult := (ArithmeticFunction.isMultiplicative_zeta.pow
    (k := k)).prod_primeFactors hn
  change (ArithmeticFunction.zeta ^ k) n = _
  rw [← hmult]
  calc
    _ = ∏ p ∈ n.primeFactors, k := by
      apply prod_congr rfl
      intro p hp
      exact divisorTupleCount_prime k p (Nat.prime_of_mem_primeFactors hp)
    _ = _ := by simp

/-- Explicit elementary logarithmic summatory majorant. -/
theorem divisorTuple_sum_le_log (k N : ℕ) :
    (∑ n ∈ Icc 1 N, (divisorTupleCount k n : ℝ)) ≤
      (N : ℝ) * (1 + Real.log N) ^ k := by
  refine (divisorTuple_sum_le k N).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ (by rw [harmonic, Rat.cast_sum]; positivity)
    (harmonic_le_one_add_log N) k

/-- A finite squarefree support has a power-of-prime-count sum bounded by
an elementary divisor-tuple sum. -/
theorem sum_squarefree_pow_le (S : Finset ℕ) (k N : ℕ)
    (hS : ∀ n ∈ S, Squarefree n) (hSN : S ⊆ Icc 1 N) :
    (∑ n ∈ S, (k : ℝ) ^ n.primeFactors.card) ≤
      (N : ℝ) * (1 + Real.log N) ^ k := by
  calc
    _ = ∑ n ∈ S, (divisorTupleCount k n : ℝ) := by
      apply sum_congr rfl
      intro n hn
      rw [divisorTupleCount_squarefree k n (hS n hn), Nat.cast_pow]
    _ ≤ ∑ n ∈ Icc 1 N, (divisorTupleCount k n : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hSN (by intros; positivity)
    _ ≤ _ := divisorTuple_sum_le_log k N

end Problem337.SelbergError

end

end OAI
