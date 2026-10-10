import OAI.NumberTheory.JointDickman.Analysis.SquarefreeEulerAnalytic
import OAI.NumberTheory.JointDickman.Analysis.ZetaPoleBranch

namespace OAI

/-! # Uniform bounds for the Euler correction on the shifted contour -/
namespace JointDickman

theorem squarefreeAnalyticFactor_uniform_bound {z σ : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hσ : 1/2 < σ) : ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, σ ≤ s.re → ‖squarefreeAnalyticFactor z s‖ ≤ C := by
  let b : Nat.Primes → ℝ := fun p => (2/(1-(2:ℝ)^(-σ)))*(p.val:ℝ)^(-2*σ)
  have hb : Summable b := squarefreePrimeLog_bound_summable hσ
  refine ⟨Real.exp (∑' p, b p),Real.exp_pos _,fun s hs => ?_⟩
  have hf := squarefreePrimeLog_summable hz hz1 (hσ.trans_le hs)
  have hl : ‖squarefreeLogFactor z s‖ ≤ ∑' p, b p := by
    calc
      _ ≤ ∑' p, ‖squarefreePrimeLog z s p‖ := norm_tsum_le_tsum_norm hf.norm
      _ ≤ _ := hf.norm.tsum_le_tsum
        (fun p => squarefreePrimeLog_uniform_bound hz hz1 (by linarith) hs p) hb
  exact (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr hl)

theorem squarefree_branch_norm_bound {z σ C : ℝ} {G : ℂ → ℂ}
    (hG : ∀ s : ℂ, σ ≤ s.re → ‖squarefreeAnalyticFactor z s‖ ≤ C)
    {s : ℂ} (hs : σ ≤ s.re) (hbranch : Complex.exp (G s) = riemannZeta s) :
    ‖squarefreeAnalyticFactor z s*Complex.exp ((z:ℂ)*G s)‖ ≤ C*‖riemannZeta s‖^z := by
  rw [norm_mul,norm_exp_real_mul_of_exp_eq z hbranch]
  exact mul_le_mul_of_nonneg_right (hG s hs) (Real.rpow_nonneg (norm_nonneg _) _)

end JointDickman

end OAI
