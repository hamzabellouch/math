import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularAnalytic

namespace OAI

/-! Regular solutions on any fixed finite radius, uniformly over bounded spectral parameters. -/

open Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem spectralRegularSourceBound_parameter (A B : ℝ →ᵇ ℂ) (cp cm lam : ℂ) :
    spectralRegularSourceBound A B (cp+Complex.I*lam) (cm-Complex.I*lam) ≤
      spectralRegularSourceBound A B cp cm+2*‖lam‖ := by
  have hp := norm_add_le cp (Complex.I*lam)
  have hm := norm_sub_le cm (Complex.I*lam)
  rw [norm_mul,Complex.norm_I,one_mul] at hp hm
  unfold spectralRegularSourceBound
  linarith

theorem exists_regular_spectral_family (d : ℕ) (R L : ℝ) (hR : 0 ≤ R) (hL : 0 ≤ L)
    (A B : ℝ →ᵇ ℂ) (cp cm : ℂ) (c : ℂ × ℂ) :
    ∃ W : ℂ → ℝ → ℂ × ℂ,
      (∀ lam, W lam 0=c ∧ deriv (W lam) 0=0 ∧ Continuous (W lam)) ∧
      (∀ lam, ‖lam‖ ≤ L → ∀ r ∈ Ioc 0 R,
        let wp := fun t => (W lam t).1
        let wm := fun t => (W lam t).2
        (deriv (deriv wp) r+((d : ℂ)/(r : ℂ)+Complex.I*(r/2 : ℝ))*deriv wp r,
         deriv (deriv wm) r+((d : ℂ)/(r : ℂ)-Complex.I*(r/2 : ℝ))*deriv wm r)=
          (A r*wp r+B r*wm r-(cp+Complex.I*lam)*wp r,
           star (B r)*wp r+star (A r)*wm r-(cm-Complex.I*lam)*wm r)) ∧
      (∀ z, ‖z‖ ≤ L → ∀ r, 0 ≤ r →
        AnalyticAt ℂ (fun lam => W lam r) z ∧
          AnalyticAt ℂ (fun lam => deriv (W lam) r) z) := by
  let α := spectralRegularSourceBound A B cp cm+2*L+1
  have hC := spectralRegularSourceBound_nonneg A B cp cm
  have hα : 0 < α := by dsimp only [α]; linarith
  have hgap (lam : ℂ) (hlam : ‖lam‖ ≤ L) :
      spectralRegularSourceBound A B (cp+Complex.I*lam) (cm-Complex.I*lam)<2*α := by
    have h := spectralRegularSourceBound_parameter A B cp cm lam
    dsimp only [α]
    linarith
  refine ⟨spectralRegularSolution d R α hR hα A B cp cm c,?_,?_,?_⟩
  · intro lam
    have h := spectralRegularSolution_initial d R α hR hα A B cp cm c lam
    exact ⟨h.1,h.2,spectralRegularSolution_continuous d R α hR hα A B cp cm c lam⟩
  · intro lam hlam r hr
    exact spectralRegularSolution_coupled d R α hR hα A B cp cm c lam (hgap lam hlam) r hr
  · intro z hz r hr
    exact ⟨spectralRegularSolution_analyticAt d R α hR hα A B cp cm z c r hr (hgap z hz),
      spectralRegularSolution_deriv_analyticAt d R α hR hα A B cp cm z c r hr (hgap z hz)⟩

end DefocusingNLS

end OAI
