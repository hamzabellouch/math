import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningFrequencyGrowth
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBResidualIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OAI

/-! The near-turning oscillatory WKB error for the actual Liouville potential. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralTurning_positive_integral (h b eta omega r₀ a c : ℝ)
    (heta : 0≤eta) (hr₀ : 0<r₀) (ha : r₀<a) (hac : a≤c) (hc : c≤2*r₀)
    (hz : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0) :
    (∫ t in a..c, (5/16 : ℝ)*(spectralLiouvilleSlope eta t)^2/
        (Real.sqrt (homogeneousSpectralLocalizationFrequency h b eta omega t))^5+
      |spectralLiouvilleSecond eta t|/
        (4*(Real.sqrt (homogeneousSpectralLocalizationFrequency h b eta omega t))^3))≤
      5*(8*spectralLiouvilleSlope eta r₀)/
        (24*(Real.sqrt (homogeneousSpectralLocalizationFrequency h b eta omega a))^3)+
      (6/r₀)/(2*Real.sqrt (homogeneousSpectralLocalizationFrequency h b eta omega a)) := by
  let F := homogeneousSpectralLocalizationFrequency h b eta omega
  have ht0 (t : ℝ) (ht : t ∈ Icc a c) : 0<t := hr₀.trans (ha.trans_le ht.1)
  have hF0 (t : ℝ) (ht : t ∈ Icc a c) : 0<F t := by
    have hh := homogeneousSpectralLocalizationFrequency_strictMono h b eta omega heta
      hr₀ (ht0 t ht) (ha.trans_le ht.1)
    simpa only [hz] using hh
  have hFD (t : ℝ) (ht : t ∈ Icc a c) : HasDerivAt F (spectralLiouvilleSlope eta t) t :=
    homogeneousSpectralLocalizationFrequency_hasDerivAt h b eta omega t (ht0 t ht)
  have hFc : ContinuousOn F (Icc a c) := fun t ht => (hFD t ht).continuousAt.continuousWithinAt
  have hgc : ContinuousOn (spectralLiouvilleSlope eta) (Icc a c) :=
    fun t ht => (spectralLiouvilleSlope_hasDerivAt eta t (ht0 t ht)).continuousAt.continuousWithinAt
  have hec : ContinuousOn (spectralLiouvilleSecond eta) (Icc a c) := by
    apply continuousOn_const.sub
    apply continuousOn_const.div (continuousOn_id.pow 4)
    exact fun t ht => pow_ne_zero _ (ht0 t ht).ne'
  have hB : 0≤8*spectralLiouvilleSlope eta r₀ := by
    dsimp only [spectralLiouvilleSlope]
    positivity
  exact spectralWKB_residual_integral a c (6/r₀) (8*spectralLiouvilleSlope eta r₀) hac
    (by positivity) hB (fun t => Real.sqrt (F t)) (spectralLiouvilleSlope eta)
    (spectralLiouvilleSecond eta) (Real.continuous_sqrt.comp_continuousOn hFc) hgc hec
    (fun t ht => Real.sqrt_pos.2 (hF0 t ht))
    (fun t ht => by dsimp only [spectralLiouvilleSlope]; have := ht0 t ht; positivity)
    (fun t ht => (spectralLiouvilleSlope_near eta r₀ t heta hr₀
      (by linarith [ht.1]) (ht.2.trans hc)).2)
    (fun t ht => spectralLiouvilleSecond_near eta r₀ t heta hr₀ (by linarith [ht.1]))
    (fun t ht => (hFD t ⟨ht.1.le,ht.2.le⟩).sqrt (hF0 t ⟨ht.1.le,ht.2.le⟩).ne')

end DefocusingNLS

end OAI
