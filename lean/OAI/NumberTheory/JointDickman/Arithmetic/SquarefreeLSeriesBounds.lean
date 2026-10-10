import OAI.NumberTheory.JointDickman.Arithmetic.SquarefreeEulerFactorization
import OAI.NumberTheory.JointDickman.Arithmetic.SquarefreeEulerBound
import OAI.NumberTheory.JointDickman.Analysis.ZetaContourBounds

namespace OAI

/-! # Bounds for the original squarefree Dirichlet series on the right -/
namespace JointDickman
open Complex Set

theorem squarefreeLSeries_norm {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    ‖LSeries (fun n => (squarefreeWeight z n:ℂ)) s‖ =
      ‖squarefreeAnalyticFactor z s‖*‖riemannZeta s‖^z := by
  rw [squarefreeDirichletSeries_factorization hz hz1 hs,norm_mul,
    norm_exp_real_mul_of_exp_eq z (primeZetaLog_exp hs)]

theorem squarefreeLSeries_high_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → 3 < |s.im| →
      ‖LSeries (fun n => (squarefreeWeight z n:ℂ)) s‖ ≤ C*|s.im|^(1/2:ℝ) := by
  obtain ⟨G,hG,hGb⟩ := squarefreeAnalyticFactor_uniform_bound hz hz1 (by norm_num : (1/2:ℝ) < 1)
  obtain ⟨A,C,hA,hC,hCb⟩ := zeta_fractional_power_high_bound
  refine ⟨G*C,mul_pos hG hC,?_⟩
  intro s hs hs2 ht
  have hlog : 0 < Real.log |s.im| := Real.log_pos (by linarith)
  have hlow : 1-A/Real.log |s.im| ≤ s.re := by
    have hp := div_pos hA.1 hlog
    linarith
  have hζ := hCb z s.re s.im hz hz1 ht ⟨hlow,hs2⟩
  rw [Complex.re_add_im] at hζ
  rw [squarefreeLSeries_norm hz hz1 hs]
  calc
    _ ≤ G*(C*|s.im|^(1/2:ℝ)) := mul_le_mul (hGb s hs.le) hζ
      (Real.rpow_nonneg (norm_nonneg _) _) hG.le
    _ = _ := by ring

end JointDickman

end OAI
