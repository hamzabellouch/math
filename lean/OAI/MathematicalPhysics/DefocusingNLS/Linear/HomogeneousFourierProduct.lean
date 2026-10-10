import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSchwartzObservation

namespace OAI

/-! # The exact Fourier product formula on the physical Schwartz domain

The previously constructed physical multiplication and frequency convolution
give the radian Fourier product formula, including its normalization.
-/

open MeasureTheory
open scoped SchwartzMap Convolution

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneousFrequencyEmbedding_injective (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) :
    Function.Injective (homogeneousFrequencyEmbedding a k ha ha1 hk) := by
  let := homogeneousFourierMeasure_temperate a k ha ha1 hk
  let := homogeneousFourierMeasure_openPos a k ha1 hk
  intro f g h
  exact SchwartzMap.injective_toLp 2 (homogeneousFourierMeasure a k) h

theorem radianFourierKernel_schwartzProduct (V f : 𝓢(E, ℂ)) :
    radianFourierKernel (SchwartzMap.smulLeftCLM ℂ V f) =
      (((((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℝ) : ℂ) •
        homogeneousSchwartzConvolution (radianFourierKernel V) (radianFourierKernel f)) := by
  have ha : 0 < (1 / 2 : ℝ) := by norm_num
  have ha1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hk : (8 : ℝ) < 9 := by norm_num
  apply homogeneousFrequencyEmbedding_injective (1 / 2) 9 ha ha1 hk
  have hp := homogeneousYProduct_physicalSchwartz (1 / 2) 9 ha ha1 hk V f
  change homogeneousYProduct (1 / 2) 9 ha ha1 hk
      (homogeneousFrequencyEmbedding (1 / 2) 9 ha ha1 hk (radianFourierKernel V))
      (homogeneousFrequencyEmbedding (1 / 2) 9 ha ha1 hk (radianFourierKernel f)) =
    homogeneousFrequencyEmbedding (1 / 2) 9 ha ha1 hk
      (radianFourierKernel (SchwartzMap.smulLeftCLM ℂ V f)) at hp
  rw [homogeneousYProduct_on_Schwartz] at hp
  exact hp.symm

theorem radianFourierKernel_schwartzProduct_apply (V f : 𝓢(E, ℂ)) (ξ : E) :
    radianFourierKernel (SchwartzMap.smulLeftCLM ℂ V f) ξ =
      (((((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℝ) : ℂ) *
        ∫ η : E, radianFourierKernel V η * radianFourierKernel f (ξ - η)) := by
  rw [radianFourierKernel_schwartzProduct]
  simp only [smul_apply, smul_eq_mul, homogeneousSchwartzConvolution,
    SchwartzMap.convolution_apply, convolution_def, ContinuousLinearMap.mul_apply']

theorem schwartz_mul_sub_integrable (V f : 𝓢(E, ℂ)) (ξ : E) :
    Integrable (fun η : E => V η * f (ξ - η)) := by
  exact ConvolutionExists.of_memLp_memLp (L := ContinuousLinearMap.mul ℂ ℂ)
    (V.memLp 2) (f.memLp 2) ξ

end DefocusingNLS

end OAI
