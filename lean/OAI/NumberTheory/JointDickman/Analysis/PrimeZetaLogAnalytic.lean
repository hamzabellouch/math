import OAI.NumberTheory.JointDickman.Arithmetic.SquarefreeEulerFactorization

namespace OAI

/-! # Analyticity of the Euler logarithm in the absolutely convergent half-plane -/
namespace JointDickman

theorem primeZetaLog_summand_bound {σ : ℝ} (hσ : 1 < σ) {s : ℂ} (hs : σ ≤ s.re)
    (p : Nat.Primes) : ‖-Complex.log (1-(p.val:ℂ)^(-s))‖ ≤
      (3/2:ℝ)*(p.val:ℝ)^(-σ) := by
  have hhalf : ‖(p.val:ℂ)^(-s)‖ ≤ 1/2 := Complex.norm_prime_cpow_le_one_half p (hσ.trans_le hs)
  have hh := Complex.norm_log_one_add_half_le_self (z := -((p.val:ℂ)^(-s)))
    (by simpa only [norm_neg] using hhalf)
  rw [norm_neg]
  calc
    _ ≤ (3/2:ℝ)*‖(p.val:ℂ)^(-s)‖ := by simpa only [sub_eq_add_neg,norm_neg] using hh
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [Complex.norm_natCast_cpow_of_pos p.property.pos,Complex.neg_re]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.property.one_le) (by linarith)

theorem primeZetaLog_differentiableOn {σ : ℝ} (hσ : 1 < σ) :
    DifferentiableOn ℂ primeZetaLog {s : ℂ | σ < s.re} := by
  have hsum : Summable (fun p : Nat.Primes => (3/2:ℝ)*(p.val:ℝ)^(-σ)) := by
    exact ((Real.summable_nat_rpow.mpr (by linarith : -σ < -1)).subtype Nat.Prime).mul_left _
  apply Complex.differentiableOn_tsum_of_summable_norm hsum
  · intro p s hs
    have hw : ‖-((p.val:ℂ)^(-s))‖ < 1 := by
      rw [norm_neg]
      exact (Complex.norm_prime_cpow_le_one_half p (by dsimp at hs; linarith)).trans_lt (by norm_num)
    have hc : DifferentiableAt ℂ (fun t : ℂ => (p.val:ℂ)^(-t)) s :=
      differentiableAt_id.neg.const_cpow (Or.inl (by exact_mod_cast p.property.ne_zero))
    exact (((differentiableAt_const (1:ℂ)).sub hc).clog
      (by simpa only [Pi.add_apply,Pi.neg_apply,sub_eq_add_neg] using
        Complex.mem_slitPlane_of_norm_lt_one hw)).neg.differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re
  · intro p s hs
    exact primeZetaLog_summand_bound hσ hs.le p

theorem primeZetaLog_analyticOnNhd : AnalyticOnNhd ℂ primeZetaLog {s : ℂ | 1 < s.re} := by
  intro s hs
  have hσ : 1 < (1+s.re)/2 := by dsimp at hs; linarith
  have hm : s ∈ {t : ℂ | (1+s.re)/2 < t.re} := by dsimp at hs ⊢; linarith
  exact (primeZetaLog_differentiableOn hσ).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re) s hm

end JointDickman

end OAI
