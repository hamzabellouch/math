import OAI.NumberTheory.JointDickman.Analysis.PrimeZetaLogReal
import OAI.NumberTheory.JointDickman.Arithmetic.SquarefreeSingularFactor

namespace OAI

/-! # The real-axis polar asymptotic of the squarefree Dirichlet series -/
namespace JointDickman
open Filter
open scoped Topology

 theorem squarefree_scaled_LSeries_eq {z δ : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) (hδ : 0 < δ) :
    ((δ^z : ℝ):ℂ)*LSeries (fun n => (squarefreeWeight z n : ℂ)) ((1+δ:ℝ):ℂ) =
      ((1+δ:ℝ):ℂ)*squarefreeSingularFactor z ((1+δ:ℝ):ℂ) := by
  have hσ : 1 < 1+δ := by linarith
  have hn : riemannZeta ((1+δ:ℝ):ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using hσ)
  have hσ0 : ((1+δ:ℝ):ℂ) ≠ 0 := by exact_mod_cast (show 1+δ ≠ 0 by linarith)
  have hσ1 : ((1+δ:ℝ):ℂ) ≠ 1 := by exact_mod_cast (show 1+δ ≠ 1 by linarith)
  have hH : zetaPoleFactor ((1+δ:ℝ):ℂ) = (δ:ℂ)*riemannZeta ((1+δ:ℝ):ℂ) := by
    rw [zetaPoleFactor_eq hσ1]
    push_cast
    ring
  have hp : ((δ^z:ℝ):ℂ) = Complex.exp ((z:ℂ)*(Real.log δ:ℂ)) := by
    rw [Real.rpow_def_of_pos hδ,Complex.ofReal_exp,Complex.ofReal_mul,mul_comm]
  rw [squarefreeDirichletSeries_real_factorization hz hz1 hσ,
    squarefreeSingularFactor,hH,Complex.log_ofReal_mul hδ hn,mul_add,Complex.exp_add,hp]
  field_simp

 theorem squarefree_LSeries_polar_tendsto {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    Tendsto (fun δ : ℝ => ((δ^z : ℝ):ℂ)*
      LSeries (fun n => (squarefreeWeight z n : ℂ)) ((1+δ:ℝ):ℂ)) (𝓝[>] 0)
      (𝓝 ((squarefreeLeadingConstant z * Real.Gamma z : ℝ):ℂ)) := by
  have ht : Tendsto (fun δ : ℝ => ((1+δ:ℝ):ℂ)) (𝓝[>] 0) (𝓝 (1:ℂ)) := by
    have h : Tendsto (fun δ : ℝ => (δ:ℂ)) (𝓝[>] 0) (𝓝 (0:ℂ)) :=
      (Complex.continuous_ofReal.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    simpa only [Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_zero,add_zero] using h.const_add 1
  have hK := (squarefreeSingularFactor_analyticAt_one hz.le hz1).continuousAt.tendsto.comp ht
  have h := ht.mul hK
  rw [one_mul,squarefreeSingularFactor_one hz hz1] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (squarefree_scaled_LSeries_eq hz.le hz1 hδ).symm

end JointDickman

end OAI
