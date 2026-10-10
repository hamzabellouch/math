import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningNearPhase
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningFarPhase

namespace OAI

/-! Uniform real phase integrals on the complete outer intervals. -/

open Set MeasureTheory
namespace DefocusingNLS

private theorem phase_continuous (sign h b eta omega a c : ℝ) (ha : 0<a)
    (hF : ∀ t ∈ Icc a c, 0<sign*homogeneousSpectralLocalizationFrequency h b eta omega t) :
    ContinuousOn (fun t => 1/Real.sqrt (sign*homogeneousSpectralLocalizationFrequency h b eta omega t))
      (Icc a c) := by
  have hFc : ContinuousOn (homogeneousSpectralLocalizationFrequency h b eta omega) (Icc a c) :=
    fun t ht => (homogeneousSpectralLocalizationFrequency_hasDerivAt h b eta omega t
      (ha.trans_le ht.1)).continuousAt.continuousWithinAt
  exact continuousOn_const.div (Real.continuous_sqrt.comp_continuousOn (continuousOn_const.mul hFc))
    (fun t ht => (Real.sqrt_pos.2 (hF t ht)).ne')

theorem spectralTurning_positive_outer_phase (ell : ℕ) (h b omega r₀ d M E : ℝ)
    (hh : h^2=1) (hb : 0≤b) (hb1 : b≤1) (hr₀ : 0<r₀) (hd : 0<d) (hM : 0<M)
    (hMd : M*d≤r₀) (hE : 2*r₀≤E) (hscale : E^2=256*max ((ell : ℝ)+1) omega)
    (hz : homogeneousSpectralLocalizationFrequency h b ((ell : ℝ)*(ell+10)) omega r₀=0) :
    (∫ t in (r₀+M*d)..E, 1/Real.sqrt
      (homogeneousSpectralLocalizationFrequency h b ((ell : ℝ)*(ell+10)) omega t))≤288 := by
  let eta : ℝ := (ell : ℝ)*(ell+10)
  let a := r₀+M*d
  let f := fun t => 1/Real.sqrt (homogeneousSpectralLocalizationFrequency h b eta omega t)
  have heta : 0≤eta := by dsimp only [eta]; positivity
  have ha : r₀<a := by dsimp only [a]; nlinarith
  have ha0 : 0<a := hr₀.trans ha
  have hac : a≤2*r₀ := by dsimp only [a]; linarith
  have hF (t : ℝ) (ht : t ∈ Icc a E) :
      0<homogeneousSpectralLocalizationFrequency h b eta omega t := by
    have hp := homogeneousSpectralLocalizationFrequency_strictMono h b eta omega heta
      hr₀ (ha0.trans_le ht.1) (ha.trans_le ht.1)
    simpa only [eta,hz] using hp
  have hf : ContinuousOn f (Icc a E) := by
    simpa only [one_mul] using phase_continuous 1 h b eta omega a E ha0
      (fun t ht => by simpa only [one_mul] using hF t ht)
  have hiL : IntervalIntegrable f volume a (2*r₀) := (hf.mono (Icc_subset_Icc le_rfl hE)).intervalIntegrable_of_Icc hac
  have hiR : IntervalIntegrable f volume (2*r₀) E := (hf.mono (Icc_subset_Icc hac le_rfl)).intervalIntegrable_of_Icc hE
  have hnear := spectralTurning_near_phase 1 h b eta omega r₀ a (2*r₀)
    (by norm_num) heta hr₀ (by linarith) hac le_rfl hz
    (fun t ht => by simpa only [one_mul] using hF t ⟨ht.1,ht.2.trans hE⟩)
  simp only [one_mul] at hnear
  have hfar := spectralTurning_positive_far_phase ell h b omega r₀ E hh hb hb1 hr₀ hE hscale hz
  calc
    _ = (∫ t in a..(2*r₀), f t)+(∫ t in (2*r₀)..E, f t) :=
      (intervalIntegral.integral_add_adjacent_intervals hiL hiR).symm
    _ ≤ 256+32 := add_le_add hnear hfar
    _ = 288 := by norm_num

theorem spectralTurning_negative_outer_phase (h b eta omega r₀ d M a : ℝ)
    (heta : 0≤eta) (hr₀ : 0<r₀) (hd : 0<d) (hM : 0<M) (ha : 0<a)
    (hahalf : a≤r₀/2) (hMd : M*d≤r₀/2)
    (hz : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0) :
    (∫ t in a..(r₀-M*d), 1/Real.sqrt
      (-homogeneousSpectralLocalizationFrequency h b eta omega t))≤260 := by
  let c := r₀-M*d
  let f := fun t => 1/Real.sqrt (-homogeneousSpectralLocalizationFrequency h b eta omega t)
  have hhalf : r₀/2≤c := by dsimp only [c]; linarith
  have hc : c<r₀ := by dsimp only [c]; nlinarith
  have hF (t : ℝ) (ht : t ∈ Icc a c) :
      0 < -homogeneousSpectralLocalizationFrequency h b eta omega t := by
    have hp := homogeneousSpectralLocalizationFrequency_strictMono h b eta omega heta
      (ha.trans_le ht.1) hr₀ (ht.2.trans_lt hc)
    rw [hz] at hp
    linarith
  have hf : ContinuousOn f (Icc a c) := by
    simpa only [neg_one_mul] using phase_continuous (-1) h b eta omega a c ha
      (fun t ht => by simpa only [neg_one_mul] using hF t ht)
  have hiL : IntervalIntegrable f volume a (r₀/2) := (hf.mono (Icc_subset_Icc le_rfl hhalf)).intervalIntegrable_of_Icc hahalf
  have hiR : IntervalIntegrable f volume (r₀/2) c := (hf.mono (Icc_subset_Icc hahalf le_rfl)).intervalIntegrable_of_Icc hhalf
  have hnear := spectralTurning_near_phase (-1) h b eta omega r₀ (r₀/2) c
    (by norm_num) heta hr₀ le_rfl hhalf (by linarith) hz
    (fun t ht => by simpa only [neg_one_mul] using hF t ⟨hahalf.trans ht.1,ht.2⟩)
  simp only [neg_one_mul] at hnear
  have hfar := spectralTurning_negative_far_phase h b eta omega r₀ a (r₀/2)
    heta hr₀ ha hahalf le_rfl hz
  calc
    _ = (∫ t in a..(r₀/2), f t)+(∫ t in (r₀/2)..c, f t) :=
      (intervalIntegral.integral_add_adjacent_intervals hiL hiR).symm
    _ ≤ 4+256 := add_le_add hfar hnear
    _ = 260 := by norm_num

end DefocusingNLS

end OAI
