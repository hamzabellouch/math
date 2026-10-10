import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningGeometry
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningDerivativeBounds

namespace OAI

/-! On the far oscillatory side, the potential dominates its radial derivative. -/

namespace DefocusingNLS

theorem spectralTurning_far_geometry (h b eta omega r₀ r : ℝ)
    (heta : 0≤eta) (hr₀ : 0<r₀) (hr : 2*r₀≤r)
    (hz : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0) :
    r^2/32≤homogeneousSpectralLocalizationFrequency h b eta omega r ∧
    spectralLiouvilleSlope eta r≤
      4*homogeneousSpectralLocalizationFrequency h b eta omega r/r := by
  have hrp : 0<r := by linarith
  have hr2 : 0<r^2 := sq_pos_of_pos hrp
  have hr02 : 0<r₀^2 := sq_pos_of_pos hr₀
  have hsq : 4*r₀^2≤r^2 := by nlinarith
  let L := eta+99/4
  have hL : 0≤L := by dsimp only [L]; positivity
  have hdiv : 4*L/r^2≤L/r₀^2 := by
    apply (div_le_div_iff₀ hr2 hr02).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsq hL]
  have hdiv' : 4*(L/r^2)≤L/r₀^2 := by simpa only [mul_div_assoc] using hdiv
  have hterm : 0≤L/r^2 := div_nonneg hL hr2.le
  have he : homogeneousSpectralLocalizationFrequency h b eta omega r=
      r^2/16-r₀^2/16+L/r₀^2-L/r^2 := by
    rw [spectralTurningFrequency_identity h b eta omega r₀ r hr₀.ne' hrp.ne' hz]
    dsimp only [L]
    field_simp
    ring
  constructor
  · rw [he]
    linarith only [hsq,hdiv',hterm,hr02]
  · apply (le_div_iff₀ hrp).mpr
    have hg : spectralLiouvilleSlope eta r*r=r^2/8+2*L/r^2 := by
      dsimp only [spectralLiouvilleSlope,L]
      field_simp [hrp.ne']
    rw [hg,he]
    simp only [mul_div_assoc]
    linarith only [hsq,hdiv',hterm,hr02]

end DefocusingNLS

end OAI
