import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemotePairRobin

namespace OAI

/-! Small incoming coordinates give the paper's physical remote endpoint condition. -/

namespace DefocusingNLS

noncomputable def spectralRemoteEndpointCoefficient (omega eta E : ℝ) : Fin 2 → ℝ :=
  ![omega/E^2+eta/E^4,-omega/E^2+eta/E^4]

theorem spectralRemote_endpoint_robin
    (b eta omega E K : ℝ) (T : SpectralRemoteOperator) (z : SpectralRemoteSpace)
    (hE : 8 ≤ E) (hb : 0 ≤ b) (hb1 : b ≤ 1) (hK : 0 ≤ K)
    (hcp : |omega/E^2+eta/E^4| ≤ 1/32)
    (hcm : |-omega/E^2+eta/E^4| ≤ 1/32)
    (hsmall : K/E^2 ≤ 1/6) (hT : ‖T-1‖ ≤ K/E^2)
    (hin : ‖spectralPhysicalDerivativeMap z‖ ≤ K/E^2*‖z‖) :
    let u := spectralRemoteInitialFrame (spectralRemoteEndpointCoefficient omega eta E) (T z)
    let q := spectralRemoteLiouvilleState E u
    ‖spectralPhysicalDerivativeMap q-
      homogeneousDiagonal
        (Complex.I*(Real.sqrt (homogeneousSpectralLocalizationFrequency 1 b eta omega E) : ℂ))
        (-Complex.I*(Real.sqrt (homogeneousSpectralLocalizationFrequency (-1) b eta omega E) : ℂ))
          (spectralPhysicalValueMap q)‖ ≤
      ((8*K+22)/E)*‖spectralPhysicalValueMap q‖ := by
  dsimp only
  let c := spectralRemoteEndpointCoefficient omega eta E
  have hc : ∀ i, |c i| ≤ 1/32 := by
    intro i
    fin_cases i
    · exact hcp
    · exact hcm
  have heps : 0 ≤ K/E^2 := div_nonneg hK (sq_nonneg E)
  have hv := spectralRemote_small_incoming_velocity c T z (K/E^2) heps hsmall hc hT hin
  simp only [c,spectralRemoteEndpointCoefficient,Matrix.cons_val_zero,Matrix.cons_val_one] at hv
  have hv' : ‖spectralPhysicalDerivativeMap (spectralRemoteInitialFrame c (T z))-
      homogeneousDiagonal
        (homogeneousSpectralLocalizationRemoteRoot 1 1 (omega/E^2+eta/E^4))
        (homogeneousSpectralLocalizationRemoteRoot (-1) 1 (-omega/E^2+eta/E^4))
        (spectralPhysicalValueMap (spectralRemoteInitialFrame c (T z)))‖ ≤
      (8*K)/E^2*‖spectralPhysicalValueMap (spectralRemoteInitialFrame c (T z))‖ := by
    convert hv using 1
    · rfl
    · dsimp only [c,spectralRemoteEndpointCoefficient]
      ring
  exact spectralRemote_pair_robin b eta omega E (8*K)
    (spectralRemoteInitialFrame c (T z)) hE hb hb1 (mul_nonneg (by norm_num) hK) hcp hcm hv'

end DefocusingNLS

end OAI
