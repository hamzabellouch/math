import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningComplexNegative
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningForbiddenFarIntegral

namespace OAI

/-! Integrated residual on the entire forbidden side of a turning point. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralTurning_outer_negative_error (h b eta omega gamma r₀ d M a : ℝ)
    (heta : 0≤eta) (hr₀ : 0<r₀) (hd : 0<d) (hM : 0<M) (ha : 0<a)
    (hahalf : a≤r₀/2) (hMd : M*d≤r₀/2)
    (hz : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0)
    (hscale : spectralLiouvilleSlope eta r₀*d^3=1) :
    (∫ t in a..(r₀-M*d),
      ‖spectralLiouvilleResidual (-1) h b eta omega gamma t‖/
        ‖spectralLiouvilleMomentum (-1) h b eta omega gamma t‖)≤
      5/(3*(Real.sqrt (M/8))^3)+3*d/(r₀*Real.sqrt (M/8))+64/(r₀*a) := by
  let c := r₀-M*d
  let f := fun t => ‖spectralLiouvilleResidual (-1) h b eta omega gamma t‖/
    ‖spectralLiouvilleMomentum (-1) h b eta omega gamma t‖
  have hhalf : r₀/2≤c := by dsimp only [c]; linarith
  have hc : c<r₀ := by dsimp only [c]; nlinarith
  have hFE (t : ℝ) (ht : t ∈ Icc a c) :
      0<(-1)*homogeneousSpectralLocalizationFrequency h b eta omega t := by
    have hh := homogeneousSpectralLocalizationFrequency_strictMono h b eta omega heta
      (ha.trans_le ht.1) hr₀ (ht.2.trans_lt hc)
    rw [hz] at hh
    linarith
  have hf : ContinuousOn f (Icc a c) :=
    (spectralLiouvilleResidual_continuousOn (-1) h b eta omega gamma a c
      (by norm_num) ha hFE).2
  have hiL : IntervalIntegrable f volume a (r₀/2) :=
    (hf.mono (Icc_subset_Icc le_rfl hhalf)).intervalIntegrable_of_Icc hahalf
  have hiR : IntervalIntegrable f volume (r₀/2) c :=
    (hf.mono (Icc_subset_Icc hahalf le_rfl)).intervalIntegrable_of_Icc hhalf
  have hnear := spectralTurning_complex_negative_integral h b eta omega gamma r₀ d M (r₀/2)
    heta hr₀ hd hM le_rfl hhalf hz hscale
  have hfar := spectralTurning_forbidden_far_integral h b eta omega gamma r₀ a (r₀/2)
    heta hr₀ ha hahalf le_rfl hz
  calc
    _ = (∫ t in a..(r₀/2), f t)+(∫ t in (r₀/2)..c, f t) :=
      (intervalIntegral.integral_add_adjacent_intervals hiL hiR).symm
    _ ≤ 64/(r₀*a)+(5/(3*(Real.sqrt (M/8))^3)+3*d/(r₀*Real.sqrt (M/8))) :=
      add_le_add hfar hnear
    _ = _ := by ring

end DefocusingNLS

end OAI
