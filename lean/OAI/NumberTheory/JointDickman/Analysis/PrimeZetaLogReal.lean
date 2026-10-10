import OAI.NumberTheory.JointDickman.Arithmetic.SquarefreeEulerFactorization

namespace OAI

/-! # The real branch of the logarithmic Euler product -/
namespace JointDickman

 theorem negative_real_log_im_zero {r : ℝ} (hr : r ≤ 1) :
    (-Complex.log (1-(r:ℂ))).im = 0 := by
  rw [← Complex.ofReal_one,← Complex.ofReal_sub,← Complex.ofReal_log (sub_nonneg.mpr hr)]
  simp

 theorem primeZetaLog_im_eq_zero {σ : ℝ} (hσ : 1 < σ) : (primeZetaLog (σ:ℂ)).im = 0 := by
  rw [primeZetaLog,Complex.im_tsum (primeZetaLog_summable (by simpa using hσ))]
  calc
    _ = ∑' _p : Nat.Primes, (0:ℝ) := by
      apply tsum_congr
      intro p
      have hp0 : 0 < (p.val:ℝ) := by exact_mod_cast p.property.pos
      have hpow : (p.val:ℝ)^(-σ) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.property.one_lt) (by linarith)
      have heq : (p.val:ℂ)^(-(σ:ℂ)) = ((p.val:ℝ)^(-σ) : ℝ) := by
        simpa only [Complex.ofReal_neg,Complex.ofReal_natCast] using (Complex.ofReal_cpow hp0.le (-σ)).symm
      rw [heq]
      exact negative_real_log_im_zero hpow.le
    _ = 0 := by simp

 theorem primeZetaLog_eq_log {σ : ℝ} (hσ : 1 < σ) :
    primeZetaLog (σ:ℂ) = Complex.log (riemannZeta (σ:ℂ)) := by
  rw [← primeZetaLog_exp (by simpa using hσ)]
  symm
  apply Complex.log_exp
  · rw [primeZetaLog_im_eq_zero hσ]
    linarith [Real.pi_pos]
  · rw [primeZetaLog_im_eq_zero hσ]
    exact Real.pi_pos.le

 theorem squarefreeDirichletSeries_real_factorization {z σ : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hσ : 1 < σ) :
    LSeries (fun n => (squarefreeWeight z n : ℂ)) (σ:ℂ) =
      squarefreeAnalyticFactor z (σ:ℂ) * Complex.exp ((z:ℂ)*Complex.log (riemannZeta (σ:ℂ))) := by
  rw [squarefreeDirichletSeries_factorization hz hz1 (by simpa using hσ),primeZetaLog_eq_log hσ]

end JointDickman

end OAI
