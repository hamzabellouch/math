import OAI.NumberTheory.JointDickman.Arithmetic.SquarefreeEulerProduct
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

namespace OAI

/-! # The squarefree Dirichlet series and its Euler product

These identities begin the analytic discharge of the two fixed-exponent
Selberg–Delange expansions. They do not assume an asymptotic for the
coefficients.
-/
namespace JointDickman
open Finset ArithmeticFunction

 theorem squarefreeLeadingConstant_pos {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    0 < squarefreeLeadingConstant z := by
  unfold squarefreeLeadingConstant
  apply div_pos _ (Real.Gamma_pos_of_pos hz)
  change 0 < ∏' p : {p : ℕ // p.Prime}, squarefreeEulerFactor z p
  rw [← squarefreeEulerProduct_eq]
  exact squarefreeEulerProduct_pos hz.le hz1

 theorem squarefreeWeight_abs_le_one {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (n : ℕ) :
    |squarefreeWeight z n| ≤ 1 := by
  simp only [squarefreeWeight,coe_mk]
  split_ifs
  · rw [abs_of_nonneg (pow_nonneg hz _)]
    exact pow_le_one₀ hz hz1
  · norm_num

noncomputable def squarefreeDirichletSummand (z : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  (squarefreeWeight z n : ℂ)*(n:ℂ)^(-s)

 theorem squarefreeDirichletSummand_term (z : ℝ) (s : ℂ) (n : ℕ) :
    squarefreeDirichletSummand z s n = LSeries.term (fun n => (squarefreeWeight z n : ℂ)) s n := by
  rw [LSeries.term_def₀ (by simp : (squarefreeWeight z 0 : ℂ) = 0)]
  rfl

 theorem squarefreeDirichletSummand_zero (z : ℝ) (s : ℂ) : squarefreeDirichletSummand z s 0 = 0 := by
  simp [squarefreeDirichletSummand]

 theorem squarefreeDirichletSummand_one (z : ℝ) (s : ℂ) : squarefreeDirichletSummand z s 1 = 1 := by
  simp [squarefreeDirichletSummand]

 theorem squarefreeDirichletSummand_mul (z : ℝ) (s : ℂ) {m n : ℕ} (hmn : m.Coprime n) :
    squarefreeDirichletSummand z s (m*n) =
      squarefreeDirichletSummand z s m * squarefreeDirichletSummand z s n := by
  unfold squarefreeDirichletSummand
  rw [(squarefreeWeight_isMultiplicative z).2 hmn]
  push_cast
  rw [← Complex.ofReal_natCast m, ← Complex.ofReal_natCast n,
    Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
  ring

 theorem squarefreeDirichletSummand_summable {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {s : ℂ} (hs : 1 < s.re) : Summable (fun n => ‖squarefreeDirichletSummand z s n‖) := by
  have h : LSeriesSummable (fun n => (squarefreeWeight z n : ℂ)) s :=
    LSeriesSummable_of_bounded_of_one_lt_re
      (fun n _ => by simpa only [Complex.norm_real,Real.norm_eq_abs] using squarefreeWeight_abs_le_one hz hz1 n) hs
  simpa only [squarefreeDirichletSummand_term] using h.norm

 theorem squarefreeDirichletSummand_prime_tsum (z : ℝ) (s : ℂ) {p : ℕ} (hp : p.Prime) :
    (∑' e : ℕ, squarefreeDirichletSummand z s (p^e)) = 1+(z:ℂ)*(p:ℂ)^(-s) := by
  have hpw : squarefreeWeight z p = z := by
    simpa only [pow_one,ite_true] using squarefreeWeight_prime_pow z hp (by omega : (1:ℕ) ≠ 0)
  rw [tsum_eq_sum (s := {0,1})]
  · simp [squarefreeDirichletSummand,hpw]
  · intro e he
    have he0 : e ≠ 0 := by intro h; apply he; simp [h]
    have he1 : e ≠ 1 := by intro h; apply he; simp [h]
    simp [squarefreeDirichletSummand,squarefreeWeight_prime_pow z hp he0,he1]

 theorem squarefreeDirichletSeries_eulerProduct {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => 1+(z:ℂ)*(p:ℂ)^(-s))
      (LSeries (fun n => (squarefreeWeight z n : ℂ)) s) := by
  have h := EulerProduct.eulerProduct_hasProd (squarefreeDirichletSummand_one z s)
    (fun {m n} hmn => squarefreeDirichletSummand_mul z s hmn)
    (squarefreeDirichletSummand_summable hz hz1 hs) (squarefreeDirichletSummand_zero z s)
  have he (p : Nat.Primes) : (∑' e : ℕ, squarefreeDirichletSummand z s (p.val^e)) =
      1+(z:ℂ)*(p:ℂ)^(-s) := squarefreeDirichletSummand_prime_tsum z s p.property
  have heq : (fun p : Nat.Primes => ∑' e : ℕ, squarefreeDirichletSummand z s (p.val^e)) =
      (fun p : Nat.Primes => 1+(z:ℂ)*(p:ℂ)^(-s)) := funext he
  rw [heq] at h
  simpa only [squarefreeDirichletSummand_term,LSeries] using h

end JointDickman

end OAI
