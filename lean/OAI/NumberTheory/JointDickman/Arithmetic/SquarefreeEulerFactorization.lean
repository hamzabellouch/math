import OAI.NumberTheory.JointDickman.Arithmetic.SquarefreeEulerAtOne

namespace OAI

/-! # Factorization of the squarefree Dirichlet series -/
namespace JointDickman

noncomputable def primeZetaLog (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, -Complex.log (1-(p.val:ℂ)^(-s))

 theorem primeZetaLog_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => -Complex.log (1-(p.val:ℂ)^(-s))) := by
  convert! (summable_riemannZetaSummand hs).of_norm.clog_one_sub.neg.subtype Nat.Prime using 1

 theorem primeZetaLog_exp {s : ℂ} (hs : 1 < s.re) : Complex.exp (primeZetaLog s) = riemannZeta s := by
  exact (EulerProduct.exp_tsum_primes_log_eq_tsum (summable_riemannZetaSummand hs)).trans
    (tsum_riemannZetaSummand hs)

 theorem squarefreeDirichletSeries_factorization {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (squarefreeWeight z n : ℂ)) s =
      squarefreeAnalyticFactor z s * Complex.exp ((z:ℂ)*primeZetaLog s) := by
  have hG := squarefreePrimeLog_summable hz hz1 (show 1/2 < s.re by linarith)
  have hZ := (primeZetaLog_summable hs).mul_left (z:ℂ)
  have hsum := (hG.add hZ).hasSum.cexp
  rw [Summable.tsum_add hG hZ,tsum_mul_left,Complex.exp_add] at hsum
  have heq (p : Nat.Primes) : Complex.exp (squarefreePrimeLog z s p+
      (z:ℂ)*(-Complex.log (1-(p.val:ℂ)^(-s)))) = 1+(z:ℂ)*(p.val:ℂ)^(-s) := by
    have hnorm : ‖(z:ℂ)*(p.val:ℂ)^(-s)‖ < 1 := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz]
      exact (mul_le_of_le_one_left (norm_nonneg _) hz1).trans_lt
        ((Complex.norm_prime_cpow_le_one_half p hs).trans_lt (by norm_num))
    have hn : 1+(z:ℂ)*(p.val:ℂ)^(-s) ≠ 0 := by
      intro he
      have hh : (z:ℂ)*(p.val:ℂ)^(-s) = -1 := by linear_combination he
      rw [hh,norm_neg,norm_one] at hnorm
      exact (lt_irrefl _ hnorm)
    have hcancel : squarefreePrimeLog z s p+(z:ℂ)*(-Complex.log (1-(p.val:ℂ)^(-s))) =
        Complex.log (1+(z:ℂ)*(p.val:ℂ)^(-s)) := by
      unfold squarefreePrimeLog squarefreeEulerLog
      ring
    rw [hcancel,Complex.exp_log hn]
  have hp : HasProd (fun p : Nat.Primes => 1+(z:ℂ)*(p.val:ℂ)^(-s))
      (squarefreeAnalyticFactor z s*Complex.exp ((z:ℂ)*primeZetaLog s)) := by
    have hf : (Complex.exp ∘ (fun p : Nat.Primes => squarefreePrimeLog z s p+
        (z:ℂ)*(-Complex.log (1-(p.val:ℂ)^(-s))))) =
        (fun p : Nat.Primes => 1+(z:ℂ)*(p.val:ℂ)^(-s)) := funext heq
    rw [hf] at hsum
    simpa only [squarefreeAnalyticFactor,squarefreeLogFactor,primeZetaLog] using hsum
  exact (squarefreeDirichletSeries_eulerProduct hz hz1 hs).unique hp

end JointDickman

end OAI
