import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningComplexIntegral
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningFarIntegral

namespace OAI

/-! Integrated residual on the entire oscillatory side of a turning point. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralTurning_outer_positive_error (h b eta omega gamma r₀ d M E : ℝ)
    (heta : 0≤eta) (hr₀ : 0<r₀) (hd : 0<d) (hM : 0<M)
    (hMd : M*d≤r₀) (hE : 2*r₀≤E)
    (hz : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0)
    (hscale : spectralLiouvilleSlope eta r₀*d^3=1) :
    (∫ t in (r₀+M*d)..E,
      ‖spectralLiouvilleResidual 1 h b eta omega gamma t‖/
        ‖spectralLiouvilleMomentum 1 h b eta omega gamma t‖)≤
      5/(3*(Real.sqrt (M/8))^3)+3*d/(r₀*Real.sqrt (M/8))+8/r₀^2 := by
  let a := r₀+M*d
  let f := fun t => ‖spectralLiouvilleResidual 1 h b eta omega gamma t‖/
    ‖spectralLiouvilleMomentum 1 h b eta omega gamma t‖
  have ha : r₀<a := by dsimp only [a]; nlinarith
  have ha0 : 0<a := hr₀.trans ha
  have hac : a≤2*r₀ := by dsimp only [a]; linarith
  have hFE (t : ℝ) (ht : t ∈ Icc a E) :
      0<1*homogeneousSpectralLocalizationFrequency h b eta omega t := by
    have hh := homogeneousSpectralLocalizationFrequency_strictMono h b eta omega heta
      hr₀ (ha0.trans_le ht.1) (ha.trans_le ht.1)
    simpa only [hz,one_mul] using hh
  have hf : ContinuousOn f (Icc a E) :=
    (spectralLiouvilleResidual_continuousOn 1 h b eta omega gamma a E
      (by norm_num) ha0 hFE).2
  have hiL : IntervalIntegrable f volume a (2*r₀) :=
    (hf.mono (Icc_subset_Icc le_rfl hE)).intervalIntegrable_of_Icc hac
  have hiR : IntervalIntegrable f volume (2*r₀) E :=
    (hf.mono (Icc_subset_Icc hac le_rfl)).intervalIntegrable_of_Icc hE
  have hnear := spectralTurning_complex_scaled_integral h b eta omega gamma r₀ d M (2*r₀)
    heta hr₀ hd hM hac le_rfl hz hscale
  have hfar := spectralTurning_far_integral h b eta omega gamma r₀ (2*r₀) E
    heta hr₀ le_rfl hE hz
  calc
    _ = (∫ t in a..(2*r₀), f t)+(∫ t in (2*r₀)..E, f t) :=
      (intervalIntegral.integral_add_adjacent_intervals hiL hiR).symm
    _ ≤ (5/(3*(Real.sqrt (M/8))^3)+3*d/(r₀*Real.sqrt (M/8)))+32/(2*r₀)^2 :=
      add_le_add hnear hfar
    _ = _ := by ring

end DefocusingNLS

end OAI
