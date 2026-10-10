import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteMatchedUniform

namespace OAI

/-! Uniform bounded Euler remainder for actual matched profiles in the
spectral counting strip. -/

open Set Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem spectralRemote_matched_uniform_bounded
    (s : ℕ → ℕ) (hs : StrictMono s) (z : ℕ → ProfileMatchingBall)
    (z0 : ProfileMatchingBall) (hz : Tendsto z atTop (𝓝 z0))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) (sigma : ℕ → ℝ)
    (hhalf : ∀ i, -(1/32 : ℝ) ≤ sigma i) (hupper : ∀ i, sigma i ≤ 4) :
    HasUniformLogJetBound L 0 (fun i t => spectralRemotePhysicalBounded
      (radialShootingA (s i)) (radialShootingB (profileMatchingParameter (z i))) (sigma i)
      (spectralDiagonalCoefficient (s i+radialInnerShootingThreshold)
        (radialMatchedProfile (s i) (z i) (Real.exp t)))
      (spectralCrossCoefficient (s i+radialInnerShootingThreshold)
        (radialMatchedProfile (s i) (z i) (Real.exp t)))) := by
  obtain ⟨hD,hC⟩ := spectralRemote_matched_uniform_coefficients s hs z z0 hz L hL
  apply spectralRemote_physical_bounded_symbol (M := 4) (by norm_num)
    (D := fun i t => spectralDiagonalCoefficient (s i+radialInnerShootingThreshold)
      (radialMatchedProfile (s i) (z i) (Real.exp t)))
    (C := fun i t => spectralCrossCoefficient (s i+radialInnerShootingThreshold)
      (radialMatchedProfile (s i) (z i) (Real.exp t)))
  · exact Eventually.of_forall (fun i => by
      have ha := radialShootingA_bounds (s i) (profileMatchingParameter (z i))
      rw [abs_of_pos ha.1]
      linarith [ha.2])
  · exact Eventually.of_forall (fun i => by
      have hb := (radialShooting_geometry (profileMatchingParameter (z i))).1
      rw [abs_of_pos (by linarith [hb.1])]
      linarith [hb.2])
  · exact Eventually.of_forall (fun i => abs_le.mpr ⟨by linarith [hhalf i],hupper i⟩)
  · exact hD.mono hL (by norm_num)
  · exact hC.mono hL (by norm_num)

end DefocusingNLS

end OAI
