import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralClassicalTestForms
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralChainScalarEquation

namespace OAI

/-! The exact source and boundary terms of the differentiated weak operator. -/

open Set MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

theorem spectralLowerOrderSlope_first_classical (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w : SpectralHarmonicWeight R) (B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (u : SpectralHarmonicPair ell R) (f g : ℝ → ℂ)
    (hf : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.fst r=f r)
    (hg : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.snd r=g r)
    (φ : 𝓢(ℝ,ℂ)) :
    inner ℂ (spectralFirstTest ell R φ)
      (spectralLowerOrderSlope ell R hR (spectralRadialWeightMultiplier R w) B
        (spectralHarmonicObservation ell R hR u))=
      -spectralClassicalRadialPairing R w.density g φ+
      star (φ R)*(B (f R,g R)).1 := by
  rw [spectralLowerOrderSlope_inner,spectralFirstTest_values,spectralFirstTest_traces,
    spectralHarmonicObservation_coordinates]
  simp only [inner_zero_left,sub_zero,add_zero,RCLike.inner_apply',starRingEnd_apply,
    star_zero,zero_mul]
  rw [spectralClassicalMultiplier_pairing ell R hR w u.snd g hg _ _
    (spectralHarmonicValue_smooth_ae ell R φ),hf R ⟨hR,le_rfl⟩,hg R ⟨hR,le_rfl⟩]

theorem spectralLowerOrderSlope_second_classical (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w : SpectralHarmonicWeight R) (B : ℂ × ℂ →L[ℂ] ℂ × ℂ)
    (u : SpectralHarmonicPair ell R) (f g : ℝ → ℂ)
    (hf : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.fst r=f r)
    (hg : ∀ r ∈ Ioc 0 R, spectralHarmonicRepresentative ell R hR u.snd r=g r)
    (φ : 𝓢(ℝ,ℂ)) :
    inner ℂ (spectralSecondTest ell R φ)
      (spectralLowerOrderSlope ell R hR (spectralRadialWeightMultiplier R w) B
        (spectralHarmonicObservation ell R hR u))=
      spectralClassicalRadialPairing R w.density f φ+
      star (φ R)*(B (f R,g R)).2 := by
  rw [spectralLowerOrderSlope_inner,spectralSecondTest_values,spectralSecondTest_traces,
    spectralHarmonicObservation_coordinates]
  simp only [inner_zero_left,zero_sub,zero_add,RCLike.inner_apply',starRingEnd_apply,
    star_zero,zero_mul,neg_neg]
  rw [spectralClassicalMultiplier_pairing ell R hR w u.fst f hf _ _
    (spectralHarmonicValue_smooth_ae ell R φ),hf R ⟨hR,le_rfl⟩,hg R ⟨hR,le_rfl⟩]

end DefocusingNLS

end OAI
