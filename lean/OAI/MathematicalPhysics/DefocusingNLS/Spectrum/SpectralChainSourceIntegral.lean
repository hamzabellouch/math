import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralChainFirstFlux

namespace OAI

/-! Integrability of the exact scalar sources of a weak first chain. -/

open Set MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralWeightedValue_test_intervalIntegrable (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w : SpectralHarmonicWeight R) (u : SpectralHarmonicEnergy ell R) (f : 𝓢(ℝ,ℂ)) :
    IntervalIntegrable (fun r => (r : ℂ)^11 *
      (star (f r)*(w.density r • spectralHarmonicValue ell R u r))) volume 0 R := by
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hR.le).mpr
    (spectralRadial_integrableOn R _
      (spectralWeightedTest_integrable _ _ w.radial_measurable w.bound w.radial_bound
        (spectralHarmonicValue ell R u)
        (spectralHarmonicValue ell R (spectralHarmonicSmoothEmbedding ell R f))
        f (spectralHarmonicValue_smooth_ae ell R f)))

theorem spectralSecondSource_test_intervalIntegrable (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R) (c ζ : ℂ) (f : 𝓢(ℝ,ℂ)) :
    IntervalIntegrable (fun r => star (f r)*spectralSecondSource ell R w u c ζ r) volume 0 R := by
  have hi₁ := (intervalIntegrable_iff_integrableOn_Icc_of_le hR.le).mpr
    (spectralAngular_integrableOn R _ (spectralAngularTest_integrable ell R w u.snd f))
  have hi₂ := spectralWeightedValue_test_intervalIntegrable ell R hR w u.fst f
  convert hi₁.add (hi₂.const_mul (c-ζ)) using 1
  funext r
  dsimp only [spectralSecondSource]
  ring

theorem spectralSecondChainSource_integral (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w : SpectralHarmonicWeight R) (u₀ u₁ : SpectralHarmonicPair ell R) (c ζ : ℂ) (f : 𝓢(ℝ,ℂ)) :
    (∫ r in (0 : ℝ)..R, star (f r)*spectralSecondChainSource ell R hR w u₀ u₁ c ζ r) =
      (∫ r in (0 : ℝ)..R, star (f r)*spectralSecondSource ell R w u₁ c ζ r) -
      (∫ r in (0 : ℝ)..R, (r : ℂ)^11 *
        (star (f r)*(w.density r • spectralHarmonicValue ell R u₀.fst r))) := by
  rw [← intervalIntegral.integral_sub
    (spectralSecondSource_test_intervalIntegrable ell R hR w u₁ c ζ f)
    (spectralWeightedValue_test_intervalIntegrable ell R hR w u₀.fst f)]
  apply intervalIntegral.integral_congr_ae
  have hsrc := (ae_restrict_iff' measurableSet_Icc).mp (spectralSecondSource_ae ell R hR w u₁ c ζ)
  have hv := (ae_restrict_iff' measurableSet_Icc).mp (spectralHarmonicRepresentative_ae ell R hR u₀.fst)
  filter_upwards [hsrc,hv] with r hs hr hmem
  rw [uIoc_of_le hR.le] at hmem
  have hm : r ∈ Icc (0 : ℝ) R := ⟨hmem.1.le,hmem.2⟩
  rw [hs hm]
  dsimp only [spectralSecondChainSource]
  rw [hr hm]
  ring

theorem spectralFirstChainSource_integral (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w : SpectralHarmonicWeight R) (u₀ u₁ : SpectralHarmonicPair ell R) (c ζ : ℂ) (f : 𝓢(ℝ,ℂ)) :
    (∫ r in (0 : ℝ)..R, star (f r)*spectralFirstChainSource ell R hR w u₀ u₁ c ζ r) =
      (∫ r in (0 : ℝ)..R, star (f r)*
        spectralSecondSource ell R w (spectralSwapPair ell R u₁) (-c) (-ζ) r) +
      (∫ r in (0 : ℝ)..R, (r : ℂ)^11 *
        (star (f r)*(w.density r • spectralHarmonicValue ell R u₀.snd r))) := by
  rw [← intervalIntegral.integral_add
    (spectralSecondSource_test_intervalIntegrable ell R hR w (spectralSwapPair ell R u₁) (-c) (-ζ) f)
    (spectralWeightedValue_test_intervalIntegrable ell R hR w u₀.snd f)]
  apply intervalIntegral.integral_congr_ae
  have hsrc := (ae_restrict_iff' measurableSet_Icc).mp
    (spectralSecondSource_ae ell R hR w (spectralSwapPair ell R u₁) (-c) (-ζ))
  have hv := (ae_restrict_iff' measurableSet_Icc).mp (spectralHarmonicRepresentative_ae ell R hR u₀.snd)
  filter_upwards [hsrc,hv] with r hs hr hmem
  rw [uIoc_of_le hR.le] at hmem
  have hm : r ∈ Icc (0 : ℝ) R := ⟨hmem.1.le,hmem.2⟩
  rw [hs hm]
  dsimp only [spectralFirstChainSource]
  rw [hr hm]
  ring

end DefocusingNLS

end OAI
