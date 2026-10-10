import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningRemoteScale
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningForbiddenGeometry
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBPhaseLowerBound

namespace OAI

/-! Uniform phase integrals on both far intervals. The oscillatory bound uses
exactly the remote scale 16 sqrt(max(ell+1,omega)) chosen in the paper. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralTurning_positive_far_phase (ell : ℕ) (h b omega r₀ E : ℝ)
    (hh : h^2=1) (hb : 0≤b) (hb1 : b≤1) (hr₀ : 0<r₀) (hE : 2*r₀≤E)
    (hscale : E^2=256*max ((ell : ℝ)+1) omega)
    (hz : homogeneousSpectralLocalizationFrequency h b ((ell : ℝ)*(ell+10)) omega r₀=0) :
    (∫ t in (2*r₀)..E, 1/Real.sqrt
      (homogeneousSpectralLocalizationFrequency h b ((ell : ℝ)*(ell+10)) omega t))≤32 := by
  let F := homogeneousSpectralLocalizationFrequency h b ((ell : ℝ)*(ell+10)) omega
  let L := Real.sqrt (F (2*r₀))
  have heta : 0≤(ell : ℝ)*(ell+10) := by positivity
  have hFpos : 0<F (2*r₀) := by
    have hd := homogeneousSpectralLocalizationFrequency_strictMono h b _ omega heta
      hr₀ (show 0<2*r₀ by positivity) (show r₀<2*r₀ by linarith)
    simpa only [hz] using hd
  have hL : 0<L := Real.sqrt_pos.2 hFpos
  have hL2 : L^2=F (2*r₀) := Real.sq_sqrt hFpos.le
  have hS := spectralTurning_remote_scale ell h b omega r₀ hh hb hb1 hr₀ hz
  have hEr : E≤32*L := by
    have hE0 : 0≤E := by linarith
    nlinarith
  have hp : ContinuousOn (fun t => Real.sqrt (F t)) (Icc (2*r₀) E) := by
    apply Real.continuous_sqrt.comp_continuousOn
    intro t ht
    exact (homogeneousSpectralLocalizationFrequency_hasDerivAt h b _ omega t
      (by linarith [ht.1])).continuousAt.continuousWithinAt
  have hbound (t : ℝ) (ht : t ∈ Icc (2*r₀) E) : L≤Real.sqrt (F t) := by
    apply Real.sqrt_le_sqrt
    exact (homogeneousSpectralLocalizationFrequency_strictMono h b _ omega heta).monotoneOn
      (by change 0<2*r₀; positivity) (by change 0<t; linarith [ht.1]) ht.1
  have hi := spectralWKB_phase_of_lower (2*r₀) E L hE hL _ hp hbound
  calc
    _ ≤ (E-2*r₀)/L := hi
    _ ≤ E/L := (div_le_div_iff_of_pos_right hL).2 (by linarith)
    _ ≤ 32 := (div_le_iff₀ hL).2 (by nlinarith)

theorem spectralTurning_negative_far_phase (h b eta omega r₀ a c : ℝ)
    (heta : 0≤eta) (hr₀ : 0<r₀) (ha : 0<a) (hac : a≤c) (hc : c≤r₀/2)
    (hz : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0) :
    (∫ t in a..c, 1/Real.sqrt (-homogeneousSpectralLocalizationFrequency h b eta omega t))≤4 := by
  let F := homogeneousSpectralLocalizationFrequency h b eta omega
  have hp : ContinuousOn (fun t => Real.sqrt (-F t)) (Icc a c) := by
    apply Real.continuous_sqrt.comp_continuousOn
    apply ContinuousOn.neg
    intro t ht
    exact (homogeneousSpectralLocalizationFrequency_hasDerivAt h b eta omega t
      (ha.trans_le ht.1)).continuousAt.continuousWithinAt
  have hbound (t : ℝ) (ht : t ∈ Icc a c) : r₀/8≤Real.sqrt (-F t) := by
    have hb := (spectralTurning_forbidden_far h b eta omega r₀ t heta hr₀
      (ha.trans_le ht.1) (ht.2.trans hc) hz).1
    have hFp : 0≤-F t := (by positivity : (0 : ℝ)≤r₀^2/32).trans hb
    have hsq := Real.sq_sqrt hFp
    have hsn := Real.sqrt_nonneg (-F t)
    nlinarith
  have hi := spectralWKB_phase_of_lower a c (r₀/8) hac (by positivity) _ hp hbound
  calc
    _ ≤ (c-a)/(r₀/8) := hi
    _ ≤ 4 := (div_le_iff₀ (by positivity : 0<r₀/8)).2 (by linarith)

end DefocusingNLS

end OAI
