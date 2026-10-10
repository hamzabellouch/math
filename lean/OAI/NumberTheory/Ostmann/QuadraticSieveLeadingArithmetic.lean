import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import OAI.NumberTheory.Ostmann.QuadraticSieveGaussEvaluation
import OAI.NumberTheory.Ostmann.QuadraticSieveSignedSupport

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped ArithmeticFunction.Moebius

noncomputable def leadingDivisorCoefficient (d q : ℕ) : ℂ :=
  ∑ e ∈ d.divisors, (μ e : ℂ) / (Real.sqrt (e : ℝ) : ℂ) * (jacobiSym (e : ℤ) q : ℂ)

noncomputable def leadingSignCoefficient (q : ℕ) : ℂ :=
  ∑ a ∈ signedSquarefreeMultipliers, (jacobiSym a q : ℂ) *
    (1 - (Real.sign (a : ℝ) : ℂ) * Complex.I) / (Real.sqrt |(a : ℝ)| : ℂ)

theorem sum_divisors_coprime_product {m n : ℕ} (h : Nat.Coprime m n) (f : ℕ → ℂ) :
    (∑ d ∈ (m * n).divisors, f d) = ∑ e ∈ m.divisors, ∑ d ∈ n.divisors, f (e * d) := by
  rw [h.divisors_mul]
  rw [Finset.sum_map]
  change (∑ x ∈ (m.divisors ×ˢ n.divisors).attach, f (x.val.1 * x.val.2)) = _
  rw [Finset.sum_attach (m.divisors ×ˢ n.divisors) (fun x : ℕ × ℕ => f (x.1 * x.2)),
    Finset.sum_product]

theorem leadingDivisorCoefficient_mul {m n : ℕ} (h : Nat.Coprime m n) (q : ℕ) :
    leadingDivisorCoefficient (m * n) q =
      leadingDivisorCoefficient m q * leadingDivisorCoefficient n q := by
  rw [leadingDivisorCoefficient, sum_divisors_coprime_product h]
  unfold leadingDivisorCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hed : Nat.Coprime e d := h.of_dvd (Nat.mem_divisors.mp he).1 (Nat.mem_divisors.mp hd).1
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hed,
    Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg e), Nat.cast_mul, jacobiSym.mul_left]
  push_cast
  ring

theorem leadingDivisorCoefficient_two_mul (d q : ℕ) (hd : Odd d) :
    leadingDivisorCoefficient (2 * d) q =
      (1 - (jacobiSym 2 q : ℂ) / (Real.sqrt 2 : ℂ)) * leadingDivisorCoefficient d q := by
  rw [leadingDivisorCoefficient_mul (Nat.coprime_two_left.mpr hd)]
  congr 1
  norm_num [leadingDivisorCoefficient, Nat.prime_two.divisors,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  ring

theorem leadingSign_gauss_identity {q : ℕ} [NeZero q] (hq : Odd q) (hsq : Squarefree q) :
    gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar * leadingSignCoefficient q *
      (1 - (jacobiSym 2 q : ℂ) / (Real.sqrt 2 : ℂ)) = (Real.sqrt (q : ℝ) : ℂ) := by
  have h2cop : (2 : ℤ).gcd q = 1 := by
    change ((2 : ℕ) : ℤ).gcd (q : ℤ) = 1
    rw [Int.gcd_natCast_natCast]
    exact (Nat.coprime_two_left.mpr hq).gcd_eq_one
  have hneg2 : jacobiSym (-2) q = jacobiSym (-1) q * jacobiSym 2 q := by
    rw [← jacobiSym.mul_left]
    norm_num
  have hs2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hs20 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
  have hjneg : jacobiSym (-1) q = if q % 4 = 1 then 1 else -1 := by
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hq) with hm | hm
    · rw [jacobiSym.at_neg_one hq, ZMod.χ₄_nat_one_mod_four hm, ite_eq_left hm]
    · rw [jacobiSym.at_neg_one hq, ZMod.χ₄_nat_three_mod_four hm, ite_eq_right (by omega)]
  rw [jacobi_gauss_evaluation hq hsq]
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hq) with hm | hm <;>
    rcases jacobiSym.eq_one_or_neg_one h2cop with hj | hj
  all_goals
    simp only [leadingSignCoefficient, signedSquarefreeMultipliers]
    norm_num [hneg2, hjneg, hm, hj, Real.sign, Int.sign]
    field_simp
    ring_nf
    simp only [hs2, Complex.I_sq]
    ring

end Ostmann.QuadraticSieve

end OAI
