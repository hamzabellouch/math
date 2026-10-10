import Mathlib
import OAI.Probability.LatticeSurface.Brownian.BrownianPathSupport

namespace OAI

namespace BrownianForcing

open MeasureTheory ProbabilityTheory Set

abbrev VectorPath (E : Type*) [TopologicalSpace E] := C(Set.Icc (0:ℝ) 1,E)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

instance : MeasurableSpace (VectorPath E) := borel (VectorPath E)

instance : BorelSpace (VectorPath E) := ⟨rfl⟩

noncomputable def twoPieceVector (d e : E) : VectorPath E :=
  ⟨fun t => min (2*(t:ℝ)) 1 • d + max (2*(t:ℝ)-1) 0 • e,by fun_prop⟩

noncomputable def scalarEval (t : Set.Icc (0:ℝ) 1) (v : E) : StrongDual ℝ (VectorPath E) :=
  (innerSL ℝ v).comp (ContinuousMap.evalCLM ℝ t)

end BrownianForcing

namespace BrownianForcing

open MeasureTheory ProbabilityTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma twoPieceVector_half (d e : E) : twoPieceVector d e halfTime = d := by
  norm_num [twoPieceVector,halfTime]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma twoPieceVector_last (d e : E) : twoPieceVector d e lastTime = d+e := by
  norm_num [twoPieceVector,lastTime]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma twoPieceVector_zero : twoPieceVector (0:E) 0 = 0 := by ext t; simp [twoPieceVector]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma scalarEval_twoPiece (d e v : E) (t : Set.Icc (0:ℝ) 1) :
    scalarEval t v (twoPieceVector d e) = twoPiece (inner ℝ v d) (inner ℝ v e) t := by
  simp [scalarEval,twoPiece,twoPieceVector,inner_add_right,inner_smul_right]

lemma varianceTwo_representer (μ : Measure (VectorPath E)) [IsGaussian μ]
    (hμ : (∫ f, f ∂μ) = 0)
    (hcov : ∀ (s t : Set.Icc (0:ℝ) 1) (v w : E),
      cov[scalarEval s v,scalarEval t w;μ] = 2*min (s:ℝ) (t:ℝ)*inner ℝ v w)
    (d e : E) :
    ∀ M : StrongDual ℝ (VectorPath E),
      cov[(scalarEval halfTime (d-e) + scalarEval lastTime e : StrongDual ℝ (VectorPath E)),M;μ] = M (twoPieceVector d e) := by
  let L : StrongDual ℝ (VectorPath E) := scalarEval halfTime (d-e)+scalarEval lastTime e
  have he (t : Set.Icc (0:ℝ) 1) (v : E) :
      cov[L,scalarEval t v;μ] = scalarEval t v (twoPieceVector d e) := by
    change cov[(scalarEval halfTime (d-e) : VectorPath E → ℝ)+
      (scalarEval lastTime e : VectorPath E → ℝ),scalarEval t v;μ] = _
    have hp (s : Set.Icc (0:ℝ) 1) (w : E) : MemLp (scalarEval s w) 2 μ := by
      simpa using ((IsGaussian.hasGaussianLaw_id (μ := μ)).map (scalarEval s w)).memLp_two
    rw [covariance_add_left (hp _ _) (hp _ _) (hp _ _),hcov,hcov,
      scalarEval_twoPiece,inner_sub_left]
    rw [real_inner_comm v d,real_inner_comm v e]
    convert twoPiece_kernel (inner ℝ v d) (inner ℝ v e) t using 1
    dsimp [halfTime,lastTime]
    ring
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
