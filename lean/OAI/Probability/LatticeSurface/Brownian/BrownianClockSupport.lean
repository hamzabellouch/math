import Mathlib
import OAI.Probability.LatticeSurface.Brownian.BrownianVector

namespace OAI

namespace BrownianForcing

open MeasureTheory ProbabilityTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

lemma shortClock_representer (μ : Measure (VectorPath E)) [IsGaussian μ]
    (hμ : (∫ f, f ∂μ) = 0) (τ : ℝ) (hτ : 0<τ)
    (hcov : ∀ (s t : Set.Icc (0:ℝ) 1) (v w : E),
      cov[scalarEval s v,scalarEval t w;μ] = (2*τ)*min (s:ℝ) (t:ℝ)*inner ℝ v w)
    (d e : E) :
    ∀ M : StrongDual ℝ (VectorPath E),
      cov[(τ⁻¹ • (scalarEval halfTime (d-e) + scalarEval lastTime e) : StrongDual ℝ (VectorPath E)),M;μ] = M (twoPieceVector d e) := by
  let L₀ : StrongDual ℝ (VectorPath E) := scalarEval halfTime (d-e)+scalarEval lastTime e
  let L : StrongDual ℝ (VectorPath E) := τ⁻¹ • L₀
  have he (t : Set.Icc (0:ℝ) 1) (v : E) :
      cov[L,scalarEval t v;μ] = scalarEval t v (twoPieceVector d e) := by
    change cov[(fun f => τ⁻¹*(L₀ f)),scalarEval t v;μ] = _
    rw [covariance_const_mul_left]
    change τ⁻¹*cov[(scalarEval halfTime (d-e) : VectorPath E → ℝ)+
      (scalarEval lastTime e : VectorPath E → ℝ),scalarEval t v;μ] = _
    have hp (s : Set.Icc (0:ℝ) 1) (w : E) : MemLp (scalarEval s w) 2 μ := by
      simpa using ((IsGaussian.hasGaussianLaw_id (μ := μ)).map (scalarEval s w)).memLp_two
    rw [covariance_add_left (hp _ _) (hp _ _) (hp _ _),hcov,hcov,
      scalarEval_twoPiece,inner_sub_left]
    rw [real_inner_comm v d,real_inner_comm v e]
    have hk := twoPiece_kernel (inner ℝ v d) (inner ℝ v e) t
    dsimp [halfTime,lastTime] at *
    calc
      _ = (2*min (1/2 : ℝ) t)*(inner ℝ v d-inner ℝ v e) +
        (2*min (1:ℝ) t)*inner ℝ v e := by field_simp [ne_of_gt hτ]
      _ = _ := by convert hk using 1; ring
  have hv : (∫ f, L f • f ∂μ) = twoPieceVector d e := by
    ext t
    apply ext_inner_left ℝ
    intro v
    change scalarEval t v (∫ f, L f • f ∂μ) = scalarEval t v (twoPieceVector d e)
    rw [covariance_vector μ hμ L,he]
  intro M
  rw [← covariance_vector μ hμ L M,hv]

end BrownianForcing

end OAI
