import OAI.NumberTheory.TwoPoint.Fourier.ModFivePrimes
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace OAI

/-! Exact finite reductions for the fixed modulus-five prime input.

The only primes-versus-prime-powers loss is the existing elementary
Chebyshev bound. These identities convert quantitative Dirichlet L-function
estimates into the selected logarithmically weighted prime estimates.
-/

namespace TwoPointCorrelations

open Finset
open scoped BigOperators Classical

def modFiveResidue (one : Bool) (n : ℕ) : Prop :=
  if one then n % 5 = 1 else n % 5 ≠ 1

noncomputable def modFiveMangoldtWeight (one : Bool) (n : ℕ) : ℝ :=
  if modFiveResidue one n then ArithmeticFunction.vonMangoldt n else 0

noncomputable def modFivePsi (one : Bool) (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 0 ⌊x⌋₊, modFiveMangoldtWeight one n

noncomputable def modFiveTwistedPsi (χ : DirichletCharacter ℂ 5) (x : ℝ) : ℂ :=
  ∑ n ∈ Icc 0 ⌊x⌋₊,
    (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod 5)

lemma modFivePrime_iff (one : Bool) (n : ℕ) :
    ModFivePrime one n ↔ n.Prime ∧ modFiveResidue one n := by
  rfl

lemma modFive_logWeight_eq (one : Bool) (n : ℕ) :
    modFiveLogWeight one n =
      if modFiveResidue one n then (if n.Prime then Real.log n else 0) else 0 := by
  by_cases hp : n.Prime <;> by_cases hr : modFiveResidue one n <;>
    simp [modFiveLogWeight, modFivePrime_iff, hp, hr]

lemma modFive_weight_difference (one : Bool) (n : ℕ) :
    modFiveMangoldtWeight one n - modFiveLogWeight one n =
      if modFiveResidue one n ∧ ¬n.Prime then ArithmeticFunction.vonMangoldt n else 0 := by
  rw [modFive_logWeight_eq]
  by_cases hp : n.Prime
  · simp [modFiveMangoldtWeight, hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
  · by_cases hr : modFiveResidue one n <;> simp [modFiveMangoldtWeight, hp, hr]

lemma modFive_weight_difference_nonneg (one : Bool) (n : ℕ) :
    0 ≤ modFiveMangoldtWeight one n - modFiveLogWeight one n := by
  rw [modFive_weight_difference]
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · rfl

lemma modFive_weight_difference_le (one : Bool) (n : ℕ) :
    modFiveMangoldtWeight one n - modFiveLogWeight one n ≤
      ArithmeticFunction.vonMangoldt n - (if n.Prime then Real.log n else 0) := by
  rw [modFive_weight_difference]
  by_cases hp : n.Prime
  · simp [hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
  · simp only [hp, ↓reduceIte, sub_zero]
    split_ifs
    · rfl
    · exact ArithmeticFunction.vonMangoldt_nonneg

/-- Restricting the prime-power error to either selection cannot increase it. -/
theorem modFivePsi_sub_theta_bounds (one : Bool) (x : ℝ) :
    0 ≤ modFivePsi one x - modFiveTheta one x ∧
      modFivePsi one x - modFiveTheta one x ≤ Chebyshev.psi x - Chebyshev.theta x := by
  have hsum : modFivePsi one x - modFiveTheta one x =
      ∑ n ∈ Icc 0 ⌊x⌋₊,
        (modFiveMangoldtWeight one n - modFiveLogWeight one n) := by
    simp only [modFivePsi, modFiveTheta, sum_sub_distrib]
  rw [hsum]
  constructor
  · exact sum_nonneg fun n _ => modFive_weight_difference_nonneg one n
  · rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc, sum_filter,
      ← sum_sub_distrib]
    exact sum_le_sum fun n _ => modFive_weight_difference_le one n

/-- The elementary loss in passing from a von Mangoldt estimate to primes. -/
theorem modFivePsi_sub_theta_abs_le (one : Bool) {x : ℝ} (hx : 1 ≤ x) :
    |modFivePsi one x - modFiveTheta one x| ≤ 2 * Real.sqrt x * Real.log x := by
  rw [abs_of_nonneg (modFivePsi_sub_theta_bounds one x).1]
  exact (modFivePsi_sub_theta_bounds one x).2.trans (Chebyshev.psi_sub_theta_le hx)

lemma modFiveMangoldtWeight_complement (n : ℕ) :
    modFiveMangoldtWeight false n + modFiveMangoldtWeight true n =
      ArithmeticFunction.vonMangoldt n := by
  by_cases hn : n % 5 = 1 <;> simp [modFiveMangoldtWeight, modFiveResidue, hn]

lemma modFivePsi_complement (x : ℝ) :
    modFivePsi false x + modFivePsi true x = Chebyshev.psi x := by
  rw [modFivePsi, modFivePsi, ← sum_add_distrib, Chebyshev.psi_eq_sum_Icc]
  exact sum_congr rfl fun n _ => modFiveMangoldtWeight_complement n

lemma modFive_character_sum (n : ℕ) :
    (∑ χ : DirichletCharacter ℂ 5, χ (n : ZMod 5)) =
      if n % 5 = 1 then (4 : ℂ) else 0 := by
  have heq : (n : ZMod 5) = 1 ↔ n % 5 = 1 := by
    simpa only [Nat.cast_one, Nat.mod_eq_of_lt (by decide : 1 < 5)] using
      (ZMod.natCast_eq_natCast_iff' n 1 5)
  simp only [DirichletCharacter.sum_characters_eq, heq]
  norm_num [Nat.totient_prime (by decide : Nat.Prime 5)]

/-- Exact character expansion; no asymptotic input is used here. -/
theorem modFivePsi_true_character_sum (x : ℝ) :
    (4 : ℂ) * (modFivePsi true x : ℂ) =
      ∑ χ : DirichletCharacter ℂ 5, modFiveTwistedPsi χ x := by
  simp only [modFivePsi, modFiveTwistedPsi, Complex.ofReal_sum, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro n hn
  rw [← mul_sum, modFive_character_sum]
  by_cases h : n % 5 = 1 <;>
    simp [modFiveMangoldtWeight, modFiveResidue, h, mul_comm]

lemma sqrt_mul_log_le_exp_sqrt (c : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    Real.sqrt x * Real.log x ≤
      4 * Real.exp (c ^ 2) * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hy : 0 ≤ Real.log x := Real.log_nonneg hx
  have hsquare := sq_nonneg (Real.sqrt (Real.log x) / 2 - c)
  have hsqrt := Real.sq_sqrt hy
  have hcs : c * Real.sqrt (Real.log x) ≤ Real.log x / 4 + c ^ 2 := by
    nlinarith
  have hlog : Real.log x ≤ 4 * Real.exp (Real.log x / 4) := by
    have he := Real.add_one_le_exp (Real.log x / 4)
    linarith
  have hexp : Real.exp (-Real.log x / 4) ≤
      Real.exp (c ^ 2) * Real.exp (-c * Real.sqrt (Real.log x)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hid : Real.sqrt x * Real.exp (Real.log x / 4) =
      x * Real.exp (-Real.log x / 4) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hxp]
    conv_rhs => lhs; rw [← Real.exp_log hxp]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    Real.sqrt x * Real.log x ≤ Real.sqrt x * (4 * Real.exp (Real.log x / 4)) :=
      mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg x)
    _ = 4 * (x * Real.exp (-Real.log x / 4)) := by rw [← hid]; ring
    _ ≤ 4 * (x * (Real.exp (c ^ 2) *
        Real.exp (-c * Real.sqrt (Real.log x)))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hexp hxp.le) (by norm_num)
    _ = _ := by ring

/-- A quantitative estimate for the selected von Mangoldt sums gives the
exact prime estimate used by the application, with unchanged exponent. -/
theorem modFiveThetaInput_of_psi (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    (hpsi : ∀ (one : Bool) (x : ℝ), 2 ≤ x →
      |modFivePsi one x - modFiveDensity one * x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x))) :
    ModFiveThetaInput := by
  refine ⟨c, C + 8 * Real.exp (c ^ 2), hc, by positivity, ?_⟩
  intro one x hx
  have herr := modFivePsi_sub_theta_abs_le one (show 1 ≤ x by linarith)
  have habsorb := sqrt_mul_log_le_exp_sqrt c (show 1 ≤ x by linarith)
  calc
    |modFiveTheta one x - modFiveDensity one * x| =
        |(modFivePsi one x - modFiveDensity one * x) -
          (modFivePsi one x - modFiveTheta one x)| := by congr 1; ring
    _ ≤ |modFivePsi one x - modFiveDensity one * x| +
        |modFivePsi one x - modFiveTheta one x| := abs_sub _ _
    _ ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x)) +
        2 * (Real.sqrt x * Real.log x) := by
      exact add_le_add (hpsi one x hx) (by simpa [mul_assoc] using herr)
    _ ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x)) +
        2 * (4 * Real.exp (c ^ 2) * x *
          Real.exp (-c * Real.sqrt (Real.log x))) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left habsorb (show (0 : ℝ) ≤ 2 by norm_num))
    _ = _ := by ring

end TwoPointCorrelations

end OAI
