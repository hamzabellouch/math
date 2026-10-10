import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPencilComplexEquation
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicScalarPairing
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLowerOrderOperator

namespace OAI

/-! The second scalar equation may be tested across the constrained core boundary. -/

open MeasureTheory
open scoped SchwartzMap
namespace DefocusingNLS

noncomputable def spectralSecondTest (ell : ℕ) (R : ℝ) (f : 𝓢(ℝ,ℂ)) :
    SpectralHarmonicPair ell R :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ (SpectralHarmonicEnergy ell R)
    (SpectralHarmonicEnergy ell R)).symm (0,spectralHarmonicSmoothEmbedding ell R f)

theorem spectralSecondTest_core (ell : ℕ) (R l : ℝ) (f : 𝓢(ℝ,ℂ)) :
    spectralSecondTest ell R f ∈ spectralHarmonicCoreSubspace ell R l := by
  rw [spectralHarmonicCore_mem]
  change (fun r => spectralHarmonicValue ell R 0 r)=ᵐ[_] 0
  simp only [map_zero]
  exact ae_restrict_of_ae (Lp.coeFn_zero ℂ 2 (radialPressureMeasure R))

theorem spectralSecondTest_values (ell : ℕ) (R : ℝ) (f : 𝓢(ℝ,ℂ)) :
    spectralHarmonicPairValues ell R (spectralSecondTest ell R f)=
      (0,spectralHarmonicValue ell R (spectralHarmonicSmoothEmbedding ell R f)) := by
  change (spectralHarmonicValue ell R 0,_)=_
  rw [map_zero]
  rfl

theorem spectralSecondTest_derivatives (ell : ℕ) (R : ℝ) (f : 𝓢(ℝ,ℂ)) :
    spectralHarmonicPairDerivatives ell R (spectralSecondTest ell R f)=
      (0,spectralHarmonicDerivative ell R (spectralHarmonicSmoothEmbedding ell R f)) := by
  change (spectralHarmonicDerivative ell R 0,_)=_
  rw [map_zero]
  rfl

theorem spectralSecondTest_traces (ell : ℕ) (R : ℝ) (hR : 0 < R) (f : 𝓢(ℝ,ℂ)) :
    spectralHarmonicPairTraces ell R hR (spectralSecondTest ell R f)=(0,f R) := by
  change (spectralRadialTrace R hR 0,
    spectralRadialTrace R hR (spectralRadialSmoothEmbedding R f))=_
  rw [map_zero,spectralRadialTrace_smooth]

theorem spectralSecondTest_equation (ell : ℕ) (R : ℝ) (hR : 0 < R)
    (w : SpectralHarmonicWeight R) (u : SpectralHarmonicPair ell R)
    (Q A : SpectralRadialL2 R →L[ℂ] SpectralRadialL2 R) (c ζ : ℂ)
    (B : ℂ × ℂ →L[ℂ] ℂ × ℂ) (z : SpectralRadialObservationSpace R)
    (f : 𝓢(ℝ,ℂ))
    (he : spectralHarmonicPairComplexForm ell R w u (spectralSecondTest ell R f)=
      inner ℂ (spectralLowerOrderOperator ell R hR Q A c ζ B z) (spectralSecondTest ell R f)) :
    star (spectralHarmonicComplexForm ell R w u.snd (spectralHarmonicSmoothEmbedding ell R f))=
      inner ℂ (spectralHarmonicValue ell R (spectralHarmonicSmoothEmbedding ell R f)) (Q z.1.2)-
      (c-ζ)*inner ℂ (spectralHarmonicValue ell R (spectralHarmonicSmoothEmbedding ell R f)) (Q z.1.1)-
      inner ℂ (spectralHarmonicDerivative ell R (spectralHarmonicSmoothEmbedding ell R f)) (A z.1.1)+
      star (f R)*(B z.2).2 := by
  have hs := congrArg star he
  rw [spectral_star_inner,spectralLowerOrderOperator_inner] at hs
  change star (spectralHarmonicComplexForm ell R w u.fst 0+
    spectralHarmonicComplexForm ell R w u.snd (spectralHarmonicSmoothEmbedding ell R f))=_ at hs
  have hz : spectralHarmonicComplexForm ell R w u.fst 0=0 := by
    simp only [spectralHarmonicComplexForm,map_zero,inner_zero_right,add_zero]
  rw [hz,zero_add] at hs
  unfold spectralWeakPairing at hs
  rw [spectralSecondTest_values,spectralSecondTest_derivatives,spectralSecondTest_traces] at hs
  simpa only [inner_zero_left,zero_add,zero_sub,add_zero,RCLike.inner_apply',
    sub_eq_add_neg,mul_neg,neg_mul,zero_mul,star_zero,starRingEnd_apply] using hs

end DefocusingNLS

end OAI
