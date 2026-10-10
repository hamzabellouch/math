import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemotePhysicalOperator

namespace OAI

/-! The original harmonic eigenpair supplies the physical operator equation used by reduction. -/

namespace DefocusingNLS

theorem spectralRemoteEigenpairState_operator
    (a b eta : ℝ) (m : ℕ) (Q f g : ℝ → ℂ) (lam : ℂ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsHarmonicRadialEigenpair a b m Q (eta : ℂ) lam f g) (t : ℝ) :
    HasDerivAt (spectralRemoteEigenpairState f g)
      (((Real.exp t : ℂ)^2 • spectralRemotePhysicalLeading
        (spectralRemoteLeadingCoefficient (fun _ => lam.im) (fun _ => eta) 0 t)+
        spectralRemotePhysicalBounded a b lam.re
          (spectralDiagonalCoefficient m (Q (Real.exp t)))
          (spectralCrossCoefficient m (Q (Real.exp t))))
            (spectralRemoteEigenpairState f g t)) t := by
  have hd := spectralRemoteEigenpairState_hasDerivAt a b eta m Q f g lam hf hg he t
  rwa [spectralRemoteEulerField_operator] at hd

end DefocusingNLS

end OAI
