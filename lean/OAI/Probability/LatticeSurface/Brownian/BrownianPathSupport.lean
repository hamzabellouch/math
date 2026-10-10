import Mathlib
import OAI.Probability.LatticeSurface.Brownian.GaussianCovarianceSupport
import OAI.Probability.LatticeSurface.Brownian.GaussianRegression

namespace OAI

namespace BrownianForcing

open MeasureTheory ProbabilityTheory Set

abbrev Path := C(Set.Icc (0:ℝ) 1, ℝ)

instance : MeasurableSpace Path := borel Path

instance : BorelSpace Path := ⟨rfl⟩

noncomputable def halfTime : Set.Icc (0:ℝ) 1 := ⟨1/2,by norm_num⟩

def lastTime : Set.Icc (0:ℝ) 1 := ⟨1,by norm_num⟩

noncomputable def twoPiece (a b : ℝ) : Path :=
  ⟨fun t => min (2*(t:ℝ)) 1*a + max (2*(t:ℝ)-1) 0*b,by fun_prop⟩

end BrownianForcing

namespace BrownianForcing

open MeasureTheory ProbabilityTheory Set

lemma twoPiece_kernel (a b : ℝ) (t : Set.Icc (0:ℝ) 1) :
    2*(a-b)*min (1/2) (t:ℝ)+2*b*min 1 (t:ℝ) = twoPiece a b t := by
  dsimp [twoPiece]
  rw [min_eq_right t.2.2]
  rcases le_total (t:ℝ) (1/2) with ht|ht
  · rw [min_eq_right ht,min_eq_left (by linarith),max_eq_right (by linarith)]
    ring
  · rw [min_eq_left ht,min_eq_right (by linarith),max_eq_left (by linarith)]
    ring

lemma twoPiece_half (a b : ℝ) : twoPiece a b halfTime = a := by
  norm_num [twoPiece,halfTime]

lemma twoPiece_last (a b : ℝ) : twoPiece a b lastTime = a+b := by
  norm_num [twoPiece,lastTime]

lemma twoPiece_zero : twoPiece 0 0 = 0 := by ext t; simp [twoPiece]

lemma twoPiece_representer (μ : Measure Path) [IsGaussian μ]
    (hμ : (∫ f, f ∂μ) = 0)
    (hcov : ∀ s t : Set.Icc (0:ℝ) 1,
      cov[ContinuousMap.evalCLM ℝ s,ContinuousMap.evalCLM ℝ t;μ] = min (s:ℝ) (t:ℝ))
    (a b : ℝ) :
    ∀ M : StrongDual ℝ Path,
      cov[((2*(a-b)) • ContinuousMap.evalCLM ℝ halfTime +
        (2*b) • ContinuousMap.evalCLM ℝ lastTime : StrongDual ℝ Path),M;μ] = M (twoPiece a b) := by
  let L : StrongDual ℝ Path := (2*(a-b)) • ContinuousMap.evalCLM ℝ halfTime +
    (2*b) • ContinuousMap.evalCLM ℝ lastTime
  have he (t : Set.Icc (0:ℝ) 1) :
      cov[L,ContinuousMap.evalCLM ℝ t;μ] = twoPiece a b t := by
    change cov[(2*(a-b)) • (fun f : Path => f halfTime) +
      (2*b) • (fun f : Path => f lastTime),(fun f : Path => f t);μ] = _
    have hp (s : Set.Icc (0:ℝ) 1) : MemLp (fun f : Path => f s) 2 μ := by
      convert! ((IsGaussian.hasGaussianLaw_id (μ := μ)).map (ContinuousMap.evalCLM ℝ s)).memLp_two using 1
    rw [covariance_add_left ((hp _).const_smul _) ((hp _).const_smul _) (hp _),
      covariance_smul_left,covariance_smul_left]
    change 2*(a-b)*cov[ContinuousMap.evalCLM ℝ halfTime,ContinuousMap.evalCLM ℝ t;μ]+
      2*b*cov[ContinuousMap.evalCLM ℝ lastTime,ContinuousMap.evalCLM ℝ t;μ] = _
    rw [hcov,hcov]
    exact twoPiece_kernel a b t
  have hv : (∫ f, L f • f ∂μ) = twoPiece a b := by
    ext t
    change (ContinuousMap.evalCLM ℝ t) (∫ f, L f • f ∂μ) = twoPiece a b t
    rw [covariance_vector μ hμ L,he]
  intro M
  rw [← covariance_vector μ hμ L M,hv]

end BrownianForcing

end OAI
