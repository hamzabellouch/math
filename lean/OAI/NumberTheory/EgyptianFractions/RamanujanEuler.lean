import OAI.NumberTheory.EgyptianFractions.RamanujanProduct

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RamanujanEuler

open RamanujanProduct

/-- The nonzero-frequency local coefficient in the ternary prime problem. -/
def primeCoefficient (p u : ℕ) : ℂ :=
  -(if p ∣ u then (p : ℂ) - 1 else -1) / ((p : ℂ) - 1) ^ 3

/-- The usual cubic Ramanujan coefficient, extended by zero at modulus
zero. At positive modulus this is the actual unit-character sum weighted
by the cube of the Möbius-to-totient ratio. -/
def coefficient (n u : ℕ) : ℂ :=
  if hn : n = 0 then 0 else
    letI : NeZero n := ⟨hn⟩
    (ArithmeticFunction.moebius n : ℂ) ^ 3 /
      (n.totient : ℂ) ^ 3 * ramanujanSum n u

theorem coefficient_of_ne_zero {n : ℕ} [NeZero n] (u : ℕ) :
    coefficient n u = (ArithmeticFunction.moebius n : ℂ) ^ 3 /
      (n.totient : ℂ) ^ 3 * ramanujanSum n u := by
  simp only [coefficient, dite_eq_right (NeZero.ne n)]

theorem moebius_cube_squarefree {n : ℕ} (hn : Squarefree n) :
    (ArithmeticFunction.moebius n : ℂ) ^ 3 =
      ∏ _p ∈ n.primeFactors, (-1 : ℂ) := by
  have hμZ : ArithmeticFunction.moebius n =
      ∏ _p ∈ n.primeFactors, (-1 : ℤ) := by
    rw [← ArithmeticFunction.isMultiplicative_moebius.prod_primeFactors hn]
    apply Finset.prod_congr rfl
    intro p hp
    exact ArithmeticFunction.moebius_apply_prime (Nat.mem_primeFactors.mp hp).1
  have hμC : (ArithmeticFunction.moebius n : ℂ) =
      ∏ _p ∈ n.primeFactors, (-1 : ℂ) := by exact_mod_cast hμZ
  rw [hμC, ← Finset.prod_pow]
  norm_num

theorem totient_squarefree_complex {n : ℕ} (hn : Squarefree n) :
    (n.totient : ℂ) = ∏ p ∈ n.primeFactors, ((p : ℂ) - 1) := by
  have hφ : n.totient = ∏ p ∈ n.primeFactors, (p - 1) := by
    rw [Nat.totient_eq_div_primeFactors_mul n,
      Nat.prod_primeFactors_of_squarefree hn, Nat.div_self (Nat.pos_of_ne_zero hn.ne_zero),
      one_mul]
  rw [hφ, Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.cast_sub (Nat.mem_primeFactors.mp hp).1.one_le, Nat.cast_one]

/-- Exact multiplicative factorization of the analytic coefficient at
squarefree moduli. -/
theorem coefficient_squarefree {n : ℕ} (hn : Squarefree n) (u : ℕ) :
    coefficient n u = ∏ p ∈ n.primeFactors, primeCoefficient p u := by
  let : NeZero n := ⟨hn.ne_zero⟩
  rw [coefficient_of_ne_zero, moebius_cube_squarefree hn,
    totient_squarefree_complex hn, ramanujanSum_squarefree hn]
  simp only [primeCoefficient, Finset.prod_div_distrib, Finset.prod_neg,
    Finset.prod_pow, Finset.prod_const]
  ring

/-- The local coefficient plus its zero-frequency term is the familiar
real Euler factor. -/
theorem one_add_primeCoefficient (p u : ℕ) (hp : p.Prime) :
    1 + primeCoefficient p u =
      ((if p ∣ u then 1 - 1 / ((p : ℝ) - 1) ^ 2
        else 1 + 1 / ((p : ℝ) - 1) ^ 3 : ℝ) : ℂ) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  rw [← ThreePrimeLocalFactor.one_add_cubicPrimeCoefficient_eq_real p u hp,
    ThreePrimeLocalFactor.cubicPrimeCoefficient_eq,
    ThreePrimeLocalFactor.primeRamanujanSum_eq]
  rfl

/-- Exact finite Euler factorization of the cubic Ramanujan series over
the divisors of a squarefree modulus. Every summand on the left is an
actual finite unit-character sum, not an asserted asymptotic main term. -/
theorem sum_coefficient_divisors {n : ℕ} (hn : Squarefree n) (u : ℕ) :
    (∑ d ∈ n.divisors, coefficient d u) =
      ∏ p ∈ n.primeFactors,
        ((if p ∣ u then 1 - 1 / ((p : ℝ) - 1) ^ 2
          else 1 + 1 / ((p : ℝ) - 1) ^ 3 : ℝ) : ℂ) := by
  let f : ArithmeticFunction ℂ :=
    ArithmeticFunction.prodPrimeFactors (fun p => primeCoefficient p u)
  have hf : f.IsMultiplicative := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  calc
    (∑ d ∈ n.divisors, coefficient d u) = ∑ d ∈ n.divisors, f d := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
      have hds : Squarefree d := Squarefree.squarefree_of_dvd hdn hn
      rw [coefficient_squarefree hds, ArithmeticFunction.prodPrimeFactors_apply hds.ne_zero]
    _ = ∏ p ∈ n.primeFactors, (1 + f p) :=
      (hf.prodPrimeFactors_one_add_of_squarefree hn).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      have hp' : p.Prime := (Nat.mem_primeFactors.mp hp).1
      have hfp : f p = primeCoefficient p u := by
        simp [f, ArithmeticFunction.prodPrimeFactors_apply hp'.ne_zero,
          hp'.primeFactors]
      rw [hfp]
      exact one_add_primeCoefficient p u hp'

/-- The finite cubic Ramanujan sum is real; its real part is precisely
the real finite singular product. -/
theorem sum_coefficient_divisors_re {n : ℕ} (hn : Squarefree n) (u : ℕ) :
    (∑ d ∈ n.divisors, coefficient d u).re =
      ∏ p ∈ n.primeFactors,
        (if p ∣ u then 1 - 1 / ((p : ℝ) - 1) ^ 2
          else 1 + 1 / ((p : ℝ) - 1) ^ 3) := by
  rw [sum_coefficient_divisors hn u, ← Complex.ofReal_prod]
  rfl

end Problem337.RamanujanEuler

end

end OAI
