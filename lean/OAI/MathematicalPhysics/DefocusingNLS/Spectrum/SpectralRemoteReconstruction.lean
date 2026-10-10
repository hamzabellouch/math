import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemotePhysicalReduction
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteEndpoint

namespace OAI

/-! Reconstruct the physical state from the reduced coordinates before
applying the endpoint Robin estimate. -/

namespace DefocusingNLS

theorem spectralRemote_reconstruct (P T : SpectralRemoteOperator) (Y : SpectralRemoteSpace)
    (hP : IsUnit P) (hT : IsUnit T) :
    P (T (Ring.inverse T (Ring.inverse P Y))) = Y := by
  change P ((T*Ring.inverse T) (Ring.inverse P Y)) = Y
  rw [Ring.mul_inverse_cancel _ hT]
  change (P*Ring.inverse P) Y = Y
  rw [Ring.mul_inverse_cancel _ hP]
  rfl

theorem spectralRemote_exp_inv_sq (K t : ℝ) : K/(Real.exp t)^2 = K*Real.exp (-2*t) := by
  rw [div_eq_mul_inv,← Real.exp_nat_mul,← Real.exp_neg]
  congr 1
  norm_num

theorem spectralRemote_physical_robin
    (b eta omega E K : ℝ) (T : SpectralRemoteOperator) (Y : SpectralRemoteSpace)
    (hE : 8 ≤ E) (hb : 0 ≤ b) (hb1 : b ≤ 1) (hK : 0 ≤ K)
    (hcp : |omega/E^2+eta/E^4| ≤ 1/32) (hcm : |-omega/E^2+eta/E^4| ≤ 1/32)
    (hunit : IsUnit T) (hsmall : K/E^2 ≤ 1/6) (hT : ‖T-1‖ ≤ K/E^2)
    (hin : ‖spectralPhysicalDerivativeMap
      (Ring.inverse T (Ring.inverse (spectralRemoteInitialFrame
        (spectralRemoteEndpointCoefficient omega eta E)) Y))‖ ≤
      K/E^2*‖Ring.inverse T (Ring.inverse (spectralRemoteInitialFrame
        (spectralRemoteEndpointCoefficient omega eta E)) Y)‖) :
    let q := spectralRemoteLiouvilleState E Y
    ‖spectralPhysicalDerivativeMap q-
      homogeneousDiagonal
        (Complex.I*(Real.sqrt (homogeneousSpectralLocalizationFrequency 1 b eta omega E) : ℂ))
        (-Complex.I*(Real.sqrt (homogeneousSpectralLocalizationFrequency (-1) b eta omega E) : ℂ))
          (spectralPhysicalValueMap q)‖ ≤ ((8*K+22)/E)*‖spectralPhysicalValueMap q‖ := by
  let c := spectralRemoteEndpointCoefficient omega eta E
  have hc : ∀ i, |c i| ≤ 1/32 := by
    intro i
    fin_cases i
    · exact hcp
    · exact hcm
  have hP := spectralRemoteInitialFrame_unit c hc
  have hrec := spectralRemote_reconstruct (spectralRemoteInitialFrame c) T Y hP hunit
  have hh := spectralRemote_endpoint_robin b eta omega E K T
    (Ring.inverse T (Ring.inverse (spectralRemoteInitialFrame c) Y))
    hE hb hb1 hK hcp hcm hsmall hT hin
  dsimp only [c] at hrec hh
  simpa only [hrec] using hh

end DefocusingNLS

end OAI
