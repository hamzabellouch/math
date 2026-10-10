import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTestPrimitive
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Complex.RealDeriv

namespace OAI

/-! Real compact tests as Schwartz functions and as full-line radial integrals. -/

open Set MeasureTheory
open scoped SchwartzMap ContDiff
namespace DefocusingNLS

noncomputable def spectralRealSchwartzTest (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) : 𝓢(ℝ,ℂ) :=
  (hc.comp_left (g := Complex.ofReal) (by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hφ)

theorem spectralRealSchwartzTest_apply (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (r : ℝ) :
    spectralRealSchwartzTest φ hφ hc r=(φ r : ℂ) := rfl

theorem spectralRealSchwartzTest_deriv (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (r : ℝ) :
    deriv (spectralRealSchwartzTest φ hφ hc) r=((deriv φ r : ℝ) : ℂ) :=
  ((hφ.differentiable (by simp) r).hasDerivAt.ofReal_comp).deriv

theorem spectralCompactTest_integral (R : ℝ) (φ : ℝ → ℝ) (F : ℝ → ℂ)
    (hs : tsupport φ ⊆ Ioo 0 R) :
    (∫ r in (0 : ℝ)..R, φ r • F r)=∫ r, φ r • F r := by
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro r hr
  have hn : φ r ≠ 0 := by
    intro hz
    exact hr (by simp only [hz,zero_smul])
  have h := hs (subset_tsupport φ hn)
  exact ⟨h.1,h.2.le⟩

end DefocusingNLS

end OAI
