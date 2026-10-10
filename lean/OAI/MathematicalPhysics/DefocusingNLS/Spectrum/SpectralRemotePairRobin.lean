import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteScalarRobin
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteValueAbsorption

namespace OAI

/-! The two-channel Liouville Robin estimate follows from the small incoming coordinates. -/

namespace DefocusingNLS

noncomputable def spectralRemoteLiouvilleState (E : ℝ) (z : SpectralRemoteSpace) : SpectralRemoteSpace :=
  ((homogeneousSpectralLocalizationFactor 1 E*z.1.1,
    homogeneousSpectralLocalizationFactor 1 E*((E : ℂ)*z.1.2+homogeneousSpectralLocalizationSlope 1 E*z.1.1)),
   (homogeneousSpectralLocalizationFactor (-1) E*z.2.1,
    homogeneousSpectralLocalizationFactor (-1) E*((E : ℂ)*z.2.2+homogeneousSpectralLocalizationSlope (-1) E*z.2.1)))

theorem spectralRemoteLiouvilleState_value_norm (E : ℝ) (hE : 0 < E) (z : SpectralRemoteSpace) :
    ‖spectralPhysicalValueMap (spectralRemoteLiouvilleState E z)‖ =
      E^(11/2 : ℝ)*‖spectralPhysicalValueMap z‖ := by
  have hh := homogeneousDiagonal_norm (homogeneousSpectralLocalizationFactor 1 E)
    (homogeneousSpectralLocalizationFactor (-1) E) (E^(11/2 : ℝ))
      (Real.rpow_nonneg hE.le _) (homogeneousSpectralLocalizationFactor_norm 1 E hE)
      (homogeneousSpectralLocalizationFactor_norm (-1) E hE) (spectralPhysicalValueMap z)
  rw [homogeneousDiagonal_apply] at hh
  exact hh

theorem spectralRemote_pair_robin
    (b eta omega E K : ℝ) (z : SpectralRemoteSpace) (hE : 8 ≤ E)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (hK : 0 ≤ K)
    (hcp : |omega/E^2+eta/E^4| ≤ 1/32)
    (hcm : |-omega/E^2+eta/E^4| ≤ 1/32)
    (hw : ‖spectralPhysicalDerivativeMap z-
      homogeneousDiagonal
        (homogeneousSpectralLocalizationRemoteRoot 1 1 (omega/E^2+eta/E^4))
        (homogeneousSpectralLocalizationRemoteRoot (-1) 1 (-omega/E^2+eta/E^4))
        (spectralPhysicalValueMap z)‖ ≤ K/E^2*‖spectralPhysicalValueMap z‖) :
    let q := spectralRemoteLiouvilleState E z
    ‖spectralPhysicalDerivativeMap q-
      homogeneousDiagonal
        (Complex.I*(Real.sqrt (homogeneousSpectralLocalizationFrequency 1 b eta omega E) : ℂ))
        (-Complex.I*(Real.sqrt (homogeneousSpectralLocalizationFrequency (-1) b eta omega E) : ℂ))
          (spectralPhysicalValueMap q)‖ ≤
      ((K+22)/E)*‖spectralPhysicalValueMap q‖ := by
  let M := ‖spectralPhysicalValueMap z‖
  have hEp : 0 < E := by linarith
  rw [homogeneousDiagonal_apply] at hw
  change ‖(z.1.2-homogeneousSpectralLocalizationRemoteRoot 1 1 (omega/E^2+eta/E^4)*z.1.1,
    z.2.2-homogeneousSpectralLocalizationRemoteRoot (-1) 1 (-omega/E^2+eta/E^4)*z.2.1)‖ ≤ K/E^2*M at hw
  have hp := spectralRemote_scalar_robin 1 b eta omega E K M z.1.1 z.1.2
    (by norm_num) hE hb hb1 hK (by simpa only [one_mul] using hcp)
    (norm_fst_le (spectralPhysicalValueMap z))
    (by simpa only [Prod.fst,one_mul] using (norm_fst_le _).trans hw)
  have hm := spectralRemote_scalar_robin (-1) b eta omega E K M z.2.1 z.2.2
    (by norm_num) hE hb hb1 hK (by simpa only [neg_one_mul] using hcm)
    (norm_snd_le (spectralPhysicalValueMap z))
    (by simpa only [Prod.snd,neg_one_mul] using (norm_snd_le _).trans hw)
  rw [homogeneousSpectralLocalizationFactor_norm 1 E hEp] at hp
  rw [homogeneousSpectralLocalizationFactor_norm (-1) E hEp] at hm
  dsimp only
  rw [spectralRemoteLiouvilleState_value_norm E hEp]
  rw [homogeneousDiagonal_apply]
  change max
    ‖homogeneousSpectralLocalizationFactor 1 E*((E : ℂ)*z.1.2+homogeneousSpectralLocalizationSlope 1 E*z.1.1)-
      Complex.I*(Real.sqrt (homogeneousSpectralLocalizationFrequency 1 b eta omega E) : ℂ)*
        (homogeneousSpectralLocalizationFactor 1 E*z.1.1)‖
    ‖homogeneousSpectralLocalizationFactor (-1) E*((E : ℂ)*z.2.2+homogeneousSpectralLocalizationSlope (-1) E*z.2.1)-
      (-Complex.I)*(Real.sqrt (homogeneousSpectralLocalizationFrequency (-1) b eta omega E) : ℂ)*
        (homogeneousSpectralLocalizationFactor (-1) E*z.2.1)‖ ≤ ((K+22)/E)*(E^(11/2 : ℝ)*M)
  apply max_le
  · simpa only [Complex.ofReal_one,one_mul,mul_assoc,mul_left_comm,mul_comm] using hp
  · simpa only [Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul,neg_mul,mul_neg,one_mul,
      mul_assoc,mul_left_comm,mul_comm] using hm

end DefocusingNLS

end OAI
