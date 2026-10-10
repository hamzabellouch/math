import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnBounds

namespace OAI

/-! The actual no-turn frequency has the remote derivative bound used to
compare the prescribed outgoing data with the WKB branch. -/

namespace DefocusingNLS

theorem spectralNoTurn_remote_slope (b eta omega C E : ℝ)
    (hb : 0 ≤ b) (heta : 0 ≤ eta) (hw : 0 < omega) (_hC : 0 ≤ C) (hCw : C ≤ omega)
    (hE : 0 < E) (hEs : E^2 = 256*omega) (hL : eta+99/4 ≤ C*omega) :
    E^2/32 ≤ homogeneousSpectralLocalizationFrequency (-1) b eta omega E ∧
      |spectralLiouvilleSlope eta E| ≤
        4*homogeneousSpectralLocalizationFrequency (-1) b eta omega E/E := by
  let F := homogeneousSpectralLocalizationFrequency (-1) b eta omega E
  have hCE : 2*C ≤ E^2 := by nlinarith
  have hFlo : E^2/16+omega/2 ≤ F :=
    spectralNoTurn_frequency_lower b eta omega C E E hb hw hE le_rfl hL hCE
  have hL2 : eta+99/4 ≤ omega^2 := by nlinarith [mul_le_mul_of_nonneg_right hCw hw.le]
  have hE4 : E^4 = 65536*omega^2 := by
    calc
      _ = (E^2)^2 := by ring
      _ = (256*omega)^2 := by rw [hEs]
      _ = _ := by ring
  have hmul := mul_le_mul_of_nonneg_right hFlo (show 0 ≤ 4*E^2 by positivity)
  have hge : spectralLiouvilleSlope eta E*E^3 = E^4/8+2*(eta+99/4) := by
    dsimp only [spectralLiouvilleSlope]
    field_simp
  have hg0 : 0 ≤ spectralLiouvilleSlope eta E := by
    dsimp only [spectralLiouvilleSlope]
    positivity
  refine ⟨by nlinarith [sq_nonneg E],?_⟩
  rw [abs_of_nonneg hg0]
  apply (mul_le_mul_iff_left₀ (pow_pos hE 3)).mp
  rw [hge]
  have heq : (4*F/E)*E^3 = 4*F*E^2 := by field_simp
  change E^4/8+2*(eta+99/4) ≤ (4*F/E)*E^3
  rw [heq]
  nlinarith

end DefocusingNLS

end OAI
