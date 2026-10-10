import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningPotentialBound
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBPhaseIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OAI

/-! A uniform phase integral over either near-turning outer interval. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralTurning_near_phase (sign h b eta omega r₀ a c : ℝ)
    (hs : sign^2=1) (heta : 0≤eta) (hr₀ : 0<r₀)
    (ha : r₀/2≤a) (hac : a≤c) (hc : c≤2*r₀)
    (hz : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0)
    (hF : ∀ t ∈ Icc a c, 0<sign*homogeneousSpectralLocalizationFrequency h b eta omega t) :
    (∫ t in a..c, 1/Real.sqrt (sign*homogeneousSpectralLocalizationFrequency h b eta omega t))≤256 := by
  let F := homogeneousSpectralLocalizationFrequency h b eta omega
  let g := spectralLiouvilleSlope eta r₀
  let p := fun t => Real.sqrt (sign*F t)
  have hg : 0<g := by dsimp only [g,spectralLiouvilleSlope]; positivity
  have ht0 (t : ℝ) (ht : t ∈ Icc a c) : 0<t := by linarith [ht.1]
  have hD (t : ℝ) (ht : t ∈ Icc a c) : HasDerivAt F (spectralLiouvilleSlope eta t) t :=
    homogeneousSpectralLocalizationFrequency_hasDerivAt h b eta omega t (ht0 t ht)
  have hFc : ContinuousOn F (Icc a c) := fun t ht => (hD t ht).continuousAt.continuousWithinAt
  have hp : ContinuousOn p (Icc a c) := Real.continuous_sqrt.comp_continuousOn (continuousOn_const.mul hFc)
  have hp0 (t : ℝ) (ht : t ∈ Icc a c) : 0<p t := Real.sqrt_pos.2 (hF t ht)
  have hgc : ContinuousOn (spectralLiouvilleSlope eta) (Icc a c) := fun t ht =>
    (spectralLiouvilleSlope_hasDerivAt eta t (ht0 t ht)).continuousAt.continuousWithinAt
  have hbound (t : ℝ) (ht : t ∈ Icc a c) : p t≤8*g := by
    have hpot := spectralTurning_potential_slope_bound h b eta omega r₀ t heta hr₀
      (ha.trans ht.1) (ht.2.trans hc) hz
    have hsign : sign*F t≤|F t| := by
      rcases sq_eq_one_iff.mp hs with h | h
      · rw [h,one_mul]; exact le_abs_self _
      · rw [h,neg_one_mul]; exact neg_le_abs _
    have hp2 : (p t)^2=sign*F t := Real.sq_sqrt (hF t ht).le
    have hpn := (hp0 t ht).le
    nlinarith
  have hh := spectralWKB_phase_integral a c (g/8) (8*g) sign hac
    (div_pos hg (by norm_num)) hs p (spectralLiouvilleSlope eta) hp hgc hp0
    (fun t ht => (spectralLiouvilleSlope_near eta r₀ t heta hr₀
      (ha.trans ht.1) (ht.2.trans hc)).1)
    (hbound a ⟨le_rfl,hac⟩) (hbound c ⟨hac,le_rfl⟩)
    (fun t ht => ((hD t ⟨ht.1.le,ht.2.le⟩).const_mul sign).sqrt (hF t ⟨ht.1.le,ht.2.le⟩).ne')
  calc
    _ ≤ 4*(8*g)/(g/8) := hh
    _ = 256 := by field_simp [hg.ne']; norm_num

end DefocusingNLS

end OAI
