import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedSimpleKernel
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeBasisParameter
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeRadiusLog
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGaugeRobinDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFixedGaugeAnalytic

namespace OAI

/-! The exact free weak boundary matrix has the expected parameter derivative. -/

namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedFreeBoundary_analyticAt (ell : ℕ) (z : ProfileMatchingBall)
    (R : ℝ) (hLR : radialShootingR (profileMatchingParameter z) < R)
    (lam : ℂ) (hhalf : -(1/32 : ℝ) ≤ lam.re)
    (hdet : spectralValueDet
      (spectralPhysicalValueMap (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) lam R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) lam R)) ≠ 0) :
    AnalyticAt ℂ (radialMatchedFreeBoundary ell z R) lam := by
  let β := radialShootingB (profileMatchingParameter z)
  have hq (h : ℝ) : -1 < (spectralQ ell h β lam).re := by
    rw [spectralQ_re]
    linarith [Nat.cast_nonneg (α := ℝ) ell]
  have hlog : max 0 (Real.log 4/2) < Real.log R :=
    spectralFreeRadius_log R ((radialShooting_geometry (profileMatchingParameter z)).2.1.trans hLR.le)
  have hM := spectralJetRobin_analyticAt
    (fun t => spectralFreePositivePhysical ell β t R)
    (fun t => spectralFreeNegativePhysical ell β t R) lam
    (spectralFreePositivePhysical_analyticAt ell β lam (hq 1) R hlog.le)
    (spectralFreeNegativePhysical_analyticAt ell β lam (hq (-1)) R hlog.le) hdet
  exact spectralFluxBoundary_analyticAt R (radialMatchedFreeMassFunction z R)
    (radialMatchedFreeTransportFunction z R) _ lam
    (spectralGaugeRobin_analyticAt _ _ _ lam hM)

end DefocusingNLS

end OAI
