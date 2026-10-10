import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningDerivativeBounds

namespace OAI

/-! Linear control of the actual frequency on the fixed-size turning annulus. -/

open Set
namespace DefocusingNLS

theorem spectralTurningFrequency_growth (h b eta omega r₀ r : ℝ)
    (heta : 0≤eta) (hr₀ : 0<r₀) (hr : r₀≤r) (hr' : r≤2*r₀)
    (hz : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0) :
    (spectralLiouvilleSlope eta r₀/8)*(r-r₀)≤
      homogeneousSpectralLocalizationFrequency h b eta omega r ∧
    homogeneousSpectralLocalizationFrequency h b eta omega r≤
      (8*spectralLiouvilleSlope eta r₀)*(r-r₀) := by
  let F := homogeneousSpectralLocalizationFrequency h b eta omega
  have hp (t : ℝ) (ht : t ∈ Icc r₀ r) : 0<t := hr₀.trans_le ht.1
  have hd (t : ℝ) (ht : t ∈ Icc r₀ r) :
      HasDerivAt F (spectralLiouvilleSlope eta t) t :=
    homogeneousSpectralLocalizationFrequency_hasDerivAt h b eta omega t (hp t ht)
  have hc : ContinuousOn F (Icc r₀ r) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ F (interior (Icc r₀ r)) :=
    fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hbounds (t : ℝ) (ht : t ∈ Icc r₀ r) :=
    spectralLiouvilleSlope_near eta r₀ t heta hr₀ (by linarith [ht.1]) (ht.2.trans hr')
  have hl := (convex_Icc r₀ r).mul_sub_le_image_sub_of_le_deriv hc hdiff
    (fun t ht => by rw [(hd t (interior_subset ht)).deriv]; exact (hbounds t (interior_subset ht)).1)
    r₀ ⟨le_rfl,hr⟩ r ⟨hr,le_rfl⟩ hr
  have hu := (convex_Icc r₀ r).image_sub_le_mul_sub_of_deriv_le hc hdiff
    (fun t ht => by rw [(hd t (interior_subset ht)).deriv]; exact (hbounds t (interior_subset ht)).2)
    r₀ ⟨le_rfl,hr⟩ r ⟨hr,le_rfl⟩ hr
  dsimp only [F] at hl hu
  rw [hz,sub_zero] at hl hu
  exact ⟨hl,hu⟩

end DefocusingNLS

end OAI
