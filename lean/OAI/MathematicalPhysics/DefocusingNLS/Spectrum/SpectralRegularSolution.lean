import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularLiftEquation

namespace OAI

/-! Actual regular two-channel solutions obtained from the finite-radius resolvent. -/

open Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS

section
variable (d : ℕ) (R α : ℝ) (hR : 0 ≤ R) (hα : 0 < α)
  (A B : ℝ →ᵇ ℂ) (cp cm : ℂ) (c : ℂ × ℂ)

noncomputable def spectralRegularVector (lam : ℂ) : RegularSpectralSpace :=
  spectralRegularResolvent d R α hR hα A B cp cm lam
    (spectralRegularInitial R α hα.le c)

noncomputable def spectralRegularSolutionSource (lam : ℂ) : RegularSpectralSpace :=
  spectralRegularSourceCLM A B (cp+Complex.I*lam) (cm-Complex.I*lam)
    (spectralRegularVector d R α hR hα A B cp cm c lam)

noncomputable def spectralRegularSolution (lam : ℂ) : ℝ → ℂ × ℂ :=
  spectralRegularLift d α c (spectralRegularSolutionSource d R α hR hα A B cp cm c lam)

theorem spectralRegularVector_equation (lam : ℂ)
    (hgap : spectralRegularSourceBound A B (cp+Complex.I*lam) (cm-Complex.I*lam)<2*α) :
    spectralRegularVector d R α hR hα A B cp cm c lam=
      spectralRegularInitial R α hα.le c+spectralRegularPairKernel d R α hR hα
        (spectralRegularSolutionSource d R α hR hα A B cp cm c lam) :=
  spectralRegularResolvent_solve d R α hR hα A B cp cm lam hgap _

theorem spectralRegularSolution_initial (lam : ℂ) :
    spectralRegularSolution d R α hR hα A B cp cm c lam 0=c ∧
      deriv (spectralRegularSolution d R α hR hα A B cp cm c lam) 0=0 :=
  spectralRegularLift_initial d α c _

theorem spectralRegularSolution_continuous (lam : ℂ) :
    Continuous (spectralRegularSolution d R α hR hα A B cp cm c lam) :=
  spectralRegularLift_continuous d α c _

theorem spectralRegularSolution_coupled (lam : ℂ)
    (hgap : spectralRegularSourceBound A B (cp+Complex.I*lam) (cm-Complex.I*lam)<2*α)
    (r : ℝ) (hr : r ∈ Ioc 0 R) :
    let wp := fun t => (spectralRegularSolution d R α hR hα A B cp cm c lam t).1
    let wm := fun t => (spectralRegularSolution d R α hR hα A B cp cm c lam t).2
    (deriv (deriv wp) r+((d : ℂ)/(r : ℂ)+Complex.I*(r/2 : ℝ))*deriv wp r,
     deriv (deriv wm) r+((d : ℂ)/(r : ℂ)-Complex.I*(r/2 : ℝ))*deriv wm r)=
      (A r*wp r+B r*wm r-(cp+Complex.I*lam)*wp r,
       star (B r)*wp r+star (A r)*wm r-(cm-Complex.I*lam)*wm r) :=
  spectralRegularLift_coupled_equation d R α hR hα A B _ _ c _ _
    (spectralRegularVector_equation d R α hR hα A B cp cm c lam hgap) rfl r hr

theorem spectralRegularVector_analyticAt (z : ℂ)
    (hgap : spectralRegularSourceBound A B (cp+Complex.I*z) (cm-Complex.I*z)<2*α) :
    AnalyticAt ℂ (spectralRegularVector d R α hR hα A B cp cm c) z := by
  let g := spectralRegularInitial R α hα.le c
  have hT := spectralRegularResolvent_analyticAt d R α hR hα A B cp cm z hgap
  have ha := ((ContinuousLinearMap.apply ℂ RegularSpectralSpace).flip).analyticAt_bilinear
    (spectralRegularResolvent d R α hR hα A B cp cm z,g)
  exact ha.comp₂ hT analyticAt_const

theorem spectralRegularSolutionSource_analyticAt (z : ℂ)
    (hgap : spectralRegularSourceBound A B (cp+Complex.I*z) (cm-Complex.I*z)<2*α) :
    AnalyticAt ℂ (spectralRegularSolutionSource d R α hR hα A B cp cm c) z := by
  have hT := spectralRegularSourceCLM_analyticAt A B cp cm z
  have hv := spectralRegularVector_analyticAt d R α hR hα A B cp cm c z hgap
  have ha := ((ContinuousLinearMap.apply ℂ RegularSpectralSpace).flip).analyticAt_bilinear
    (spectralRegularSourceCLM A B (cp+Complex.I*z) (cm-Complex.I*z),
      spectralRegularVector d R α hR hα A B cp cm c z)
  exact ha.comp₂ hT hv

end
end DefocusingNLS

end OAI
