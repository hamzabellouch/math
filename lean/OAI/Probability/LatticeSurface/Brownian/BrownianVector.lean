import Mathlib
import OAI.Probability.LatticeSurface.Brownian.BrownianVectorSupport

namespace OAI

namespace BrownianForcing

open MeasureTheory ProbabilityTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem varianceTwo_twoPiece_tube (μ : Measure (VectorPath E)) [IsGaussian μ]
    (hμ : (∫ f, f ∂μ) = 0)
    (hcov : ∀ (s t : Set.Icc (0:ℝ) 1) (v w : E),
      cov[scalarEval s v,scalarEval t w;μ] = 2*min (s:ℝ) (t:ℝ)*inner ℝ v w)
    (d e : E) (ε : ℝ) (hε : 0 < ε) :
    0 < μ {f | ∀ t : Set.Icc (0:ℝ) 1, ‖f t-twoPieceVector d e t‖ < ε} := by
  let L : StrongDual ℝ (VectorPath E) := scalarEval halfTime (d-e)+scalarEval lastTime e
  have hball : 0 < μ (Metric.ball (twoPieceVector d e) ε) := by
    by_cases h : d=0 ∧ e=0
    · rcases h with ⟨rfl,rfl⟩
      rw [twoPieceVector_zero]
      exact gaussian_small_ball μ hμ ε hε
    · have hnon : 0 < ‖d‖^2+‖e‖^2 := by
        have hd := sq_nonneg ‖d‖
        have he := sq_nonneg ‖e‖
        by_contra hn
        have hd0 : ‖d‖=0 := by nlinarith
        have he0 : ‖e‖=0 := by nlinarith
        exact h ⟨norm_eq_zero.mp hd0,norm_eq_zero.mp he0⟩
      have hLg : 0 < L (twoPieceVector d e) := by
        change 0 < inner ℝ (d-e) (twoPieceVector d e halfTime)+inner ℝ e (twoPieceVector d e lastTime)
        rw [twoPieceVector_half,twoPieceVector_last,inner_sub_left,inner_add_right,
          real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
        linarith
      exact gaussian_representer_tube μ hμ L (twoPieceVector d e)
        (varianceTwo_representer μ hμ hcov d e) hLg ε hε
  convert hball using 1
  congr 1
  ext f
  simp only [mem_ofPred_eq,Metric.mem_ball,dist_eq_norm]
  rw [ContinuousMap.norm_lt_iff _ hε]
  simp only [ContinuousMap.sub_apply]

end BrownianForcing

end OAI
