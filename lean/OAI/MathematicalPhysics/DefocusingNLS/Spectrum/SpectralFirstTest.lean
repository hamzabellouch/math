import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSecondTest

namespace OAI

/-! The first scalar equation can be tested outside the constrained core. -/

open Set MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

noncomputable def spectralFirstTest (ell : ℕ) (R : ℝ) (f : 𝓢(ℝ,ℂ)) :
    SpectralHarmonicPair ell R :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ (SpectralHarmonicEnergy ell R)
    (SpectralHarmonicEnergy ell R)).symm (spectralHarmonicSmoothEmbedding ell R f,0)

theorem spectralFirstTest_core (ell : ℕ) (R l : ℝ) (f : 𝓢(ℝ,ℂ))
    (hf : ∀ r ≤ l, f r=0) :
    spectralFirstTest ell R f ∈ spectralHarmonicCoreSubspace ell R l := by
  rw [spectralHarmonicCore_mem]
  change ∀ᵐ r ∂(radialPressureMeasure R).restrict (Iic l),
    spectralHarmonicValue ell R (spectralHarmonicSmoothEmbedding ell R f) r=0
  rw [ae_restrict_iff' measurableSet_Iic]
  filter_upwards [spectralHarmonicValue_smooth_ae ell R f] with r hr hrl
  exact hr.trans (hf r hrl)

theorem spectralFirstTest_values (ell : ℕ) (R : ℝ) (f : 𝓢(ℝ,ℂ)) :
    spectralHarmonicPairValues ell R (spectralFirstTest ell R f)=
      (spectralHarmonicValue ell R (spectralHarmonicSmoothEmbedding ell R f),0) := by
  change (_,spectralHarmonicValue ell R 0)=_
  rw [map_zero]
  rfl

theorem spectralFirstTest_derivatives (ell : ℕ) (R : ℝ) (f : 𝓢(ℝ,ℂ)) :
    spectralHarmonicPairDerivatives ell R (spectralFirstTest ell R f)=
      (spectralHarmonicDerivative ell R (spectralHarmonicSmoothEmbedding ell R f),0) := by
  change (_,spectralHarmonicDerivative ell R 0)=_
  rw [map_zero]
  rfl

theorem spectralFirstTest_traces (ell : ℕ) (R : ℝ) (hR : 0 < R) (f : 𝓢(ℝ,ℂ)) :
    spectralHarmonicPairTraces ell R hR (spectralFirstTest ell R f)=(f R,0) := by
  change (spectralRadialTrace R hR (spectralRadialSmoothEmbedding R f),
    spectralRadialTrace R hR 0)=_
  rw [map_zero,spectralRadialTrace_smooth]

theorem spectralFirstTest_equation (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R)
    (Q A : SpectralRadialL2 R →L[ℂ] SpectralRadialL2 R) (c ζ : ℂ)
    (B : ℂ × ℂ →L[ℂ] ℂ × ℂ) (z : SpectralRadialObservationSpace R)
    (f : 𝓢(ℝ,ℂ))
    (he : spectralHarmonicPairComplexForm ell R w u (spectralFirstTest ell R f)=
      inner ℂ (spectralLowerOrderOperator ell R hR Q A c ζ B z) (spectralFirstTest ell R f)) :
    star (spectralHarmonicComplexForm ell R w u.fst (spectralHarmonicSmoothEmbedding ell R f))=
      inner ℂ (spectralHarmonicValue ell R (spectralHarmonicSmoothEmbedding ell R f)) (Q z.1.1)+
      (c-ζ)*inner ℂ (spectralHarmonicValue ell R (spectralHarmonicSmoothEmbedding ell R f)) (Q z.1.2)+
      inner ℂ (spectralHarmonicDerivative ell R (spectralHarmonicSmoothEmbedding ell R f)) (A z.1.2)+
      star (f R)*(B z.2).1 := by
  have hs := congrArg star he
  rw [spectral_star_inner,spectralLowerOrderOperator_inner] at hs
  change star (spectralHarmonicComplexForm ell R w u.fst (spectralHarmonicSmoothEmbedding ell R f)+
    spectralHarmonicComplexForm ell R w u.snd 0)=_ at hs
  have hz : spectralHarmonicComplexForm ell R w u.snd 0=0 := by
    simp only [spectralHarmonicComplexForm,map_zero,inner_zero_right,add_zero]
  rw [hz,add_zero] at hs
  unfold spectralWeakPairing at hs
  rw [spectralFirstTest_values,spectralFirstTest_derivatives,spectralFirstTest_traces] at hs
  simpa only [inner_zero_left,zero_add,sub_zero,add_zero,RCLike.inner_apply',
    zero_mul,star_zero,starRingEnd_apply] using hs

end DefocusingNLS

end OAI
