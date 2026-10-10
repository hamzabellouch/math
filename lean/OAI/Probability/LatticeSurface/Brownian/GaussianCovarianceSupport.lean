import Mathlib
import OAI.Probability.LatticeSurface.Brownian.GaussianTube

namespace OAI

namespace BrownianForcing

open MeasureTheory ProbabilityTheory Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

theorem integrable_covariance_vector (μ : Measure E) [IsGaussian μ] (L : StrongDual ℝ E) :
    Integrable (fun x => L x • x) μ := by
  have hL := (IsGaussian.hasGaussianLaw_id (μ := μ)).map L
  have h : MemLp (fun x => L x • x) 1 μ := by
    exact hL.memLp_two.smul (IsGaussian.memLp_two_id (μ := μ))
  exact h.integrable le_rfl

theorem covariance_vector (μ : Measure E) [IsGaussian μ]
    (hμ : (∫ x, x ∂μ) = 0) (L M : StrongDual ℝ E) :
    M (∫ x, L x • x ∂μ) = cov[L,M;μ] := by
  rw [← M.integral_comp_comm (integrable_covariance_vector μ L),
    covariance_eq_sub (by simpa using ((IsGaussian.hasGaussianLaw_id (μ := μ)).map L).memLp_two)
      (by simpa using ((IsGaussian.hasGaussianLaw_id (μ := μ)).map M).memLp_two)]
  have hL : (∫ x, L x ∂μ) = 0 := by
    simpa only [id_eq,hμ,map_zero] using L.integral_comp_comm (IsGaussian.integrable_id (μ := μ))
  simp only [hL,zero_mul,sub_zero,map_smul,smul_eq_mul,Pi.mul_apply]

end BrownianForcing

end OAI
