import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedFreeBoundaryDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLowerOrderDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPencilDerivative

namespace OAI

/-! The derivative load for the actual free compact pencil. -/

open Filter Topology
namespace DefocusingNLS
open ProfileCertificate

noncomputable local instance freeWeakDerivativeNormed (ell : ℕ) (R : ℝ) :
    NormedAddCommGroup (SpectralRadialObservationSpace R →L[ℂ] SpectralHarmonicPair ell R) := by
  let : NormedAddCommGroup (SpectralHarmonicPair ell R) := inferInstance
  let : NormedSpace ℂ (SpectralHarmonicPair ell R) := inferInstance
  let : NormedAddCommGroup (SpectralRadialObservationSpace R) := inferInstance
  let : NormedSpace ℂ (SpectralRadialObservationSpace R) := inferInstance
  exact ContinuousLinearMap.toNormedAddCommGroup

theorem radialMatchedFreeWeak_hasDerivAt (ell : ℕ) (z : ProfileMatchingBall)
    (hc : Continuous (radialMatchedFreeMassFunction z)) (R : ℝ)
    (hLR : radialShootingR (profileMatchingParameter z) < R)
    (w : SpectralHarmonicWeight R) (hw : w.density=radialMatchedFreeMassFunction z)
    (lam : ℂ) (hhalf : -(1/32 : ℝ) ≤ lam.re)
    (hdet : spectralValueDet
      (spectralPhysicalValueMap (spectralFreePositivePhysical ell (radialShootingB (profileMatchingParameter z)) lam R))
      (spectralPhysicalValueMap (spectralFreeNegativePhysical ell (radialShootingB (profileMatchingParameter z)) lam R)) ≠ 0) :
    let hR := (radialMatchedCore_radius_pos z).trans hLR
    HasDerivAt (fun t => radialMatchedLimitWeakOperator ell z hc R hR t
      (radialMatchedFreeBoundary ell z R t))
      (spectralLowerOrderSlope ell R hR (spectralRadialWeightMultiplier R w)
        (deriv (radialMatchedFreeBoundary ell z R) lam)) lam := by
  let hR := (radialMatchedCore_radius_pos z).trans hLR
  let a := spectralContinuousCoefficient R (radialMatchedFreeTransportFunction z)
    (continuous_const.mul (continuous_id.mul (continuous_radialAverage _ hc)))
  have hB : HasDerivAt (radialMatchedFreeBoundary ell z R)
      (deriv (radialMatchedFreeBoundary ell z R) lam) lam := (radialMatchedFreeBoundary_hasDerivAt ell z R hLR lam hhalf hdet).differentiableAt.hasDerivAt
  have h := spectralLowerOrderOperator_hasDerivAt ell R hR
    (spectralRadialWeightMultiplier R w) (spectralRadialWeightMultiplier R a) 6
    (radialMatchedFreeBoundary ell z R) _ lam hB
  have heq : (fun t => radialMatchedLimitWeakOperator ell z hc R hR t
      (radialMatchedFreeBoundary ell z R t)) =
      (fun t => spectralLowerOrderOperator ell R hR (spectralRadialWeightMultiplier R w)
        (spectralRadialWeightMultiplier R a) 6 t (radialMatchedFreeBoundary ell z R t)) := by
    funext t
    exact radialMatchedLimitWeakOperator_eq ell z hc R hR w a hw rfl t (radialMatchedFreeBoundary ell z R t)
  dsimp only
  rw [heq]
  exact h

end DefocusingNLS

end OAI
