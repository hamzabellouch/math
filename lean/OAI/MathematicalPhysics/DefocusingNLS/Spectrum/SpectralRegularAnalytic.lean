import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularSolution
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularJetOperator

namespace OAI

/-! Holomorphy of the regular radial values and derivatives at the matching boundary. -/

open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem spectralRegularLift_analyticAt (d : ℕ) (α : ℝ) (hα : 0 < α)
    (c : ℂ × ℂ) (s : ℂ → RegularSpectralSpace) (z : ℂ)
    (t : ℝ) (ht : 0 ≤ t) (hs : AnalyticAt ℂ s z) :
    AnalyticAt ℂ (fun lam => spectralRegularLift d α c (s lam) t) z := by
  have hp : AnalyticAt ℂ (fun lam => (s lam).1) z :=
    ((ContinuousLinearMap.fst ℂ (ℝ →ᵇ ℂ) (ℝ →ᵇ ℂ)).analyticAt (s z)).comp hs
  have hm : AnalyticAt ℂ (fun lam => (s lam).2) z :=
    ((ContinuousLinearMap.snd ℂ (ℝ →ᵇ ℂ) (ℝ →ᵇ ℂ)).analyticAt (s z)).comp hs
  have hpp : AnalyticAt ℂ (fun lam => spectralRegularPrimitiveEvalCLM d 1 α t hα ht (s lam).1) z :=
    ((spectralRegularPrimitiveEvalCLM d 1 α t hα ht).analyticAt ((s z).1)).comp
      (f := fun lam : ℂ => (s lam).1) (x := z) hp
  have hmm : AnalyticAt ℂ (fun lam => spectralRegularPrimitiveEvalCLM d (-1) α t hα ht (s lam).2) z :=
    ((spectralRegularPrimitiveEvalCLM d (-1) α t hα ht).analyticAt ((s z).2)).comp
      (f := fun lam : ℂ => (s lam).2) (x := z) hm
  simpa only [spectralRegularLift,spectralRegularPrimitiveEvalCLM_apply,Pi.add_apply] using
    (analyticAt_const.add hpp).prod (analyticAt_const.add hmm)

theorem spectralRegularLift_deriv_analyticAt (d : ℕ) (α : ℝ) (hα : 0 ≤ α)
    (c : ℂ × ℂ) (s : ℂ → RegularSpectralSpace) (z : ℂ)
    (t : ℝ) (ht : 0 ≤ t) (hs : AnalyticAt ℂ s z) :
    AnalyticAt ℂ (fun lam => deriv (spectralRegularLift d α c (s lam)) t) z := by
  have hp : AnalyticAt ℂ (fun lam => (s lam).1) z :=
    ((ContinuousLinearMap.fst ℂ (ℝ →ᵇ ℂ) (ℝ →ᵇ ℂ)).analyticAt (s z)).comp hs
  have hm : AnalyticAt ℂ (fun lam => (s lam).2) z :=
    ((ContinuousLinearMap.snd ℂ (ℝ →ᵇ ℂ) (ℝ →ᵇ ℂ)).analyticAt (s z)).comp hs
  have hpp : AnalyticAt ℂ (fun lam => spectralRegularSlopeEvalCLM d 1 α t hα ht (s lam).1) z :=
    ((spectralRegularSlopeEvalCLM d 1 α t hα ht).analyticAt ((s z).1)).comp
      (f := fun lam : ℂ => (s lam).1) (x := z) hp
  have hmm : AnalyticAt ℂ (fun lam => spectralRegularSlopeEvalCLM d (-1) α t hα ht (s lam).2) z :=
    ((spectralRegularSlopeEvalCLM d (-1) α t hα ht).analyticAt ((s z).2)).comp
      (f := fun lam : ℂ => (s lam).2) (x := z) hm
  simp_rw [(spectralRegularLift_hasDerivAt d α c _ t).deriv]
  simpa only [spectralRegularSlopeEvalCLM_apply] using hpp.prod hmm

theorem spectralRegularSolution_analyticAt (d : ℕ) (R α : ℝ)
    (hR : 0 ≤ R) (hα : 0 < α) (A B : ℝ →ᵇ ℂ) (cp cm z : ℂ)
    (c : ℂ × ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hgap : spectralRegularSourceBound A B (cp+Complex.I*z) (cm-Complex.I*z)<2*α) :
    AnalyticAt ℂ (fun lam => spectralRegularSolution d R α hR hα A B cp cm c lam t) z :=
  spectralRegularLift_analyticAt d α hα c _ z t ht
    (spectralRegularSolutionSource_analyticAt d R α hR hα A B cp cm c z hgap)

theorem spectralRegularSolution_deriv_analyticAt (d : ℕ) (R α : ℝ)
    (hR : 0 ≤ R) (hα : 0 < α) (A B : ℝ →ᵇ ℂ) (cp cm z : ℂ)
    (c : ℂ × ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hgap : spectralRegularSourceBound A B (cp+Complex.I*z) (cm-Complex.I*z)<2*α) :
    AnalyticAt ℂ (fun lam => deriv (spectralRegularSolution d R α hR hα A B cp cm c lam) t) z :=
  spectralRegularLift_deriv_analyticAt d α hα.le c _ z t ht
    (spectralRegularSolutionSource_analyticAt d R α hR hα A B cp cm c z hgap)

end DefocusingNLS

end OAI
