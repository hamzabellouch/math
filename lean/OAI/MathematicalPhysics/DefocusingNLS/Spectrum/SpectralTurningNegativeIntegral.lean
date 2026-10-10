import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningForbiddenGeometry
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBDecreasingIntegral
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBScaledEndpoint

namespace OAI

/-! The near-turning forbidden interval has the same uniform residual error. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralTurning_negative_scaled_integral (h b eta omega r₀ d M a : ℝ)
    (heta : 0≤eta) (hr₀ : 0<r₀) (hd : 0<d) (hM : 0<M)
    (ha : r₀/2≤a) (hac : a≤r₀-M*d)
    (hz : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0)
    (hscale : spectralLiouvilleSlope eta r₀*d^3=1) :
    (∫ t in a..(r₀-M*d), (5/16 : ℝ)*(spectralLiouvilleSlope eta t)^2/
        (Real.sqrt (-homogeneousSpectralLocalizationFrequency h b eta omega t))^5+
      |spectralLiouvilleSecond eta t|/
        (4*(Real.sqrt (-homogeneousSpectralLocalizationFrequency h b eta omega t))^3))≤
      5/(3*(Real.sqrt (M/8))^3)+3*d/(r₀*Real.sqrt (M/8)) := by
  let c := r₀-M*d
  let F := homogeneousSpectralLocalizationFrequency h b eta omega
  have hc : c<r₀ := by dsimp only [c]; nlinarith
  have ha0 : 0<a := by linarith
  have ht0 (t : ℝ) (ht : t ∈ Icc a c) : 0<t := ha0.trans_le ht.1
  have hF0 (t : ℝ) (ht : t ∈ Icc a c) : F t<0 := by
    have hh := homogeneousSpectralLocalizationFrequency_strictMono h b eta omega heta
      (ht0 t ht) hr₀ (ht.2.trans_lt hc)
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
  have hint := spectralWKB_decreasing_residual_integral a c (6/r₀)
    (8*spectralLiouvilleSlope eta r₀) hac (by positivity) hB
    (fun t => Real.sqrt (-F t)) (spectralLiouvilleSlope eta) (spectralLiouvilleSecond eta)
    (Real.continuous_sqrt.comp_continuousOn hFc.neg) hgc hec
    (fun t ht => Real.sqrt_pos.2 (neg_pos.2 (hF0 t ht)))
    (fun t ht => by dsimp only [spectralLiouvilleSlope]; have := ht0 t ht; positivity)
    (fun t ht => (spectralLiouvilleSlope_near eta r₀ t heta hr₀
      (ha.trans ht.1) (by linarith [ht.2])).2)
    (fun t ht => spectralLiouvilleSecond_near eta r₀ t heta hr₀ (ha.trans ht.1))
    (fun t ht => by
      have hh := (hFD t ⟨ht.1.le,ht.2.le⟩).neg.sqrt (neg_ne_zero.mpr (hF0 t ⟨ht.1.le,ht.2.le⟩).ne)
      simpa only [Pi.neg_apply,neg_div] using hh)
  have hcC : c ∈ Icc a c := ⟨hac,le_rfl⟩
  have hp : 0<Real.sqrt (-F c) := Real.sqrt_pos.2 (neg_pos.2 (hF0 c hcC))
  have hlow := (spectralTurning_forbidden_growth h b eta omega r₀ c heta hr₀
    (ha.trans hac) hc.le hz).1
  have hpoint : (spectralLiouvilleSlope eta r₀/8)*(M*d)≤(Real.sqrt (-F c))^2 := by
    rw [Real.sq_sqrt (neg_pos.2 (hF0 c hcC)).le]
    simpa only [c,sub_sub_cancel] using hlow
  exact hint.trans (spectralWKB_scaled_endpoint r₀ d M (Real.sqrt (-F c))
    (spectralLiouvilleSlope eta r₀) hr₀ hd hM hp
    (by dsimp only [spectralLiouvilleSlope]; positivity) hscale hpoint)

end DefocusingNLS

end OAI
