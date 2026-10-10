import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningFrequencyGrowth
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningGeometry

namespace OAI

/-! Quantitative potential bounds on the forbidden side of the turning point. -/

open Set
namespace DefocusingNLS

theorem spectralTurning_forbidden_growth (h b eta omega r₀ r : ℝ)
    (heta : 0≤eta) (hr₀ : 0<r₀) (hr : r₀/2≤r) (hr' : r≤r₀)
    (hz : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0) :
    (spectralLiouvilleSlope eta r₀/8)*(r₀-r)≤
      -homogeneousSpectralLocalizationFrequency h b eta omega r ∧
    -homogeneousSpectralLocalizationFrequency h b eta omega r≤
      (8*spectralLiouvilleSlope eta r₀)*(r₀-r) := by
  let F := homogeneousSpectralLocalizationFrequency h b eta omega
  have hp (t : ℝ) (ht : t ∈ Icc r r₀) : 0<t := by linarith [ht.1]
  have hd (t : ℝ) (ht : t ∈ Icc r r₀) :
      HasDerivAt F (spectralLiouvilleSlope eta t) t :=
    homogeneousSpectralLocalizationFrequency_hasDerivAt h b eta omega t (hp t ht)
  have hc : ContinuousOn F (Icc r r₀) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ F (interior (Icc r r₀)) :=
    fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hbounds (t : ℝ) (ht : t ∈ Icc r r₀) :=
    spectralLiouvilleSlope_near eta r₀ t heta hr₀ (hr.trans ht.1) (by linarith [ht.2])
  have hl := (convex_Icc r r₀).mul_sub_le_image_sub_of_le_deriv hc hdiff
    (fun t ht => by rw [(hd t (interior_subset ht)).deriv]; exact (hbounds t (interior_subset ht)).1)
    r ⟨le_rfl,hr'⟩ r₀ ⟨hr',le_rfl⟩ hr'
  have hu := (convex_Icc r r₀).image_sub_le_mul_sub_of_deriv_le hc hdiff
    (fun t ht => by rw [(hd t (interior_subset ht)).deriv]; exact (hbounds t (interior_subset ht)).2)
    r ⟨le_rfl,hr'⟩ r₀ ⟨hr',le_rfl⟩ hr'
  dsimp only [F] at hl hu
  rw [hz,zero_sub] at hl hu
  exact ⟨hl,hu⟩

theorem spectralTurning_forbidden_far (h b eta omega r₀ r : ℝ)
    (heta : 0≤eta) (hr₀ : 0<r₀) (hr : 0<r) (hrr : r≤r₀/2)
    (hz : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0) :
    r₀^2/32≤-homogeneousSpectralLocalizationFrequency h b eta omega r ∧
    spectralLiouvilleSlope eta r≤
      4*(-homogeneousSpectralLocalizationFrequency h b eta omega r)/r := by
  have hr2 : 0<r^2 := sq_pos_of_pos hr
  have hr02 : 0<r₀^2 := sq_pos_of_pos hr₀
  have hsq : 4*r^2≤r₀^2 := by nlinarith
  let L := eta+99/4
  have hL : 0≤L := by dsimp only [L]; positivity
  have hdiv : 4*L/r₀^2≤L/r^2 := by
    apply (div_le_div_iff₀ hr02 hr2).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsq hL]
  have hdiv' : 4*(L/r₀^2)≤L/r^2 := by simpa only [mul_div_assoc] using hdiv
  have hterm : 0≤L/r₀^2 := div_nonneg hL hr02.le
  have he : homogeneousSpectralLocalizationFrequency h b eta omega r=
      r^2/16-r₀^2/16+L/r₀^2-L/r^2 := by
    rw [spectralTurningFrequency_identity h b eta omega r₀ r hr₀.ne' hr.ne' hz]
    dsimp only [L]
    field_simp
    ring
  constructor
  · rw [he]
    linarith only [hsq,hdiv',hterm,hr02]
  · apply (le_div_iff₀ hr).mpr
    have hg : spectralLiouvilleSlope eta r*r=r^2/8+2*L/r^2 := by
      dsimp only [spectralLiouvilleSlope,L]
      field_simp [hr.ne']
    rw [hg,he]
    simp only [mul_div_assoc]
    linarith only [hsq,hdiv',hterm,hr02]

end DefocusingNLS

end OAI
