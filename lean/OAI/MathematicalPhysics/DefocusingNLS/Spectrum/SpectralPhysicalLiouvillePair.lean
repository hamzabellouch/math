import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSpectralLocalizationEquation
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteEigenpair
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemotePairRobin
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellMatchedCoupling

namespace OAI

/-! The actual radial eigenpair in the physical coordinates used by the
two scalar Green operators. -/

open Set
namespace DefocusingNLS

noncomputable def spectralPhysicalLiouvillePair (f g : ℝ → ℂ) (r : ℝ) :
    (ℂ × ℂ) × (ℂ × ℂ) :=
  (homogeneousSpectralLocalizationState 1 (fun t => (f t, deriv f t)) r,
   homogeneousSpectralLocalizationState (-1) (fun t => (g t, deriv g t)) r)

theorem spectralPhysicalLiouvillePair_remote (f g : ℝ → ℂ) (t : ℝ) :
    spectralPhysicalLiouvillePair f g (Real.exp t) =
      spectralRemoteLiouvilleState (Real.exp t) (spectralRemoteEigenpairState f g t) := by
  have hne : (Real.exp t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'
  simp only [spectralPhysicalLiouvillePair, homogeneousSpectralLocalizationState,
    spectralRemoteLiouvilleState, spectralRemoteEigenpairState, spectralRemoteEulerState]
  simp only [mul_div_cancel₀ _ hne]

theorem spectralPhysicalLiouvillePair_equation
    (a b eta : ℝ) (m : ℕ) (Q : ℝ → ℂ) (lam : ℂ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsHarmonicRadialEigenpair a b m Q (eta : ℂ) lam f g)
    (r : ℝ) (hr : 0 < r) :
    let q := spectralPhysicalLiouvillePair f g
    HasDerivAt (fun t => (q t).1)
      (spectralScalarField
        ((homogeneousSpectralLocalizationFrequency 1 b eta lam.im r : ℂ)+
          Complex.I*((a+lam.re-3 : ℝ) : ℂ)) (q r).1+
        (0,spectralShellPlusForcing m (Q r) r (q r))) r ∧
    HasDerivAt (fun t => (q t).2)
      (spectralScalarField
        ((homogeneousSpectralLocalizationFrequency (-1) b eta lam.im r : ℂ)+
          Complex.I*((-(a+lam.re-3) : ℝ) : ℂ)) (q r).2+
        (0,spectralShellMinusForcing m (Q r) r (q r))) r := by
  obtain ⟨hp,hm⟩ := homogeneousSpectralLocalization_eigenpair a b eta m Q lam f g hf hg he r hr
  constructor
  · exact hp.congr_deriv (by
      apply Prod.ext <;>
        simp [spectralPhysicalLiouvillePair, spectralScalarField, spectralShellPlusForcing]
      ring)
  · exact hm.congr_deriv (by
      apply Prod.ext <;>
        simp [spectralPhysicalLiouvillePair, spectralScalarField, spectralShellMinusForcing]
      ring)

theorem spectralPhysicalLiouvillePair_continuousOn
    (a b eta : ℝ) (m : ℕ) (Q : ℝ → ℂ) (lam : ℂ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsHarmonicRadialEigenpair a b m Q (eta : ℂ) lam f g) :
    ContinuousOn (spectralPhysicalLiouvillePair f g) (Ioi 0) := by
  intro r hr
  obtain ⟨hp,hm⟩ := spectralPhysicalLiouvillePair_equation a b eta m Q lam f g hf hg he r hr
  exact (hp.prodMk hm).continuousAt.continuousWithinAt

end DefocusingNLS

end OAI
