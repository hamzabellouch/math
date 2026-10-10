import Mathlib
import OAI.Probability.LatticeSurface.Brownian.BrownianPathSupport

namespace OAI

namespace BrownianForcing

open MeasureTheory ProbabilityTheory Set

theorem brownian_twoPiece_tube (μ : Measure Path) [IsGaussian μ]
    (hμ : (∫ f, f ∂μ) = 0)
    (hcov : ∀ s t : Set.Icc (0:ℝ) 1,
      cov[ContinuousMap.evalCLM ℝ s,ContinuousMap.evalCLM ℝ t;μ] = min (s:ℝ) (t:ℝ))
    (a b ε : ℝ) (hε : 0 < ε) :
    0 < μ {f | ∀ t : Set.Icc (0:ℝ) 1, |f t-twoPiece a b t| < ε} := by
  let L : StrongDual ℝ Path := (2*(a-b)) • ContinuousMap.evalCLM ℝ halfTime +
    (2*b) • ContinuousMap.evalCLM ℝ lastTime
  have hball : 0 < μ (Metric.ball (twoPiece a b) ε) := by
    by_cases h : a=0 ∧ b=0
    · rcases h with ⟨rfl,rfl⟩
      rw [twoPiece_zero]
      exact gaussian_small_ball μ hμ ε hε
    · have hnon : 0 < a^2+b^2 := by
        have ha := sq_nonneg a
        have hb := sq_nonneg b
        by_contra hn
        have ha0 : a=0 := by nlinarith
        have hb0 : b=0 := by nlinarith
        exact h ⟨ha0,hb0⟩
      have hLg : 0 < L (twoPiece a b) := by
        change 0 < 2*(a-b)*twoPiece a b halfTime+2*b*twoPiece a b lastTime
        rw [twoPiece_half,twoPiece_last]
        nlinarith
      exact gaussian_representer_tube μ hμ L (twoPiece a b)
        (twoPiece_representer μ hμ hcov a b) hLg ε hε
  convert hball using 1
  congr 1
  ext f
  simp only [mem_ofPred_eq,Metric.mem_ball,dist_eq_norm]
  rw [ContinuousMap.norm_lt_iff _ hε]
  simp only [ContinuousMap.sub_apply,Real.norm_eq_abs]

end BrownianForcing

end OAI
