import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousYConvolution

namespace OAI

/-! # The homogeneous algebra is the actual pointwise physical product -/

open MeasureTheory
open scoped SchwartzMap Convolution FourierTransform ZeroAtInfty

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem radianFourierIntegral_schwartzConvolution (ψ φ : 𝓢(E, ℂ)) (ξ : E) :
    radianFourierIntegral (homogeneousSchwartzConvolution ψ φ) ξ =
      radianFourierIntegral ψ ξ * radianFourierIntegral φ ξ := by
  simp only [radianFourierIntegral_eq_fourier]
  have he : (homogeneousSchwartzConvolution ψ φ : E → ℂ) =
      (ψ : E → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] (φ : E → ℂ) := by
    funext y
    exact SchwartzMap.convolution_apply _ ψ φ y
  rw [he]
  exact Real.fourier_mul_convolution_eq ψ.integrable φ.integrable _

theorem inverseRadianFourier_normalizedConvolution (ψ φ : 𝓢(E, ℂ)) (y : E) :
    inverseRadianFourier
      (((((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℝ) : ℂ) •
        (homogeneousSchwartzConvolution ψ φ : E → ℂ)) y =
      inverseRadianFourier ψ y * inverseRadianFourier φ y := by
  rw [inverseRadianFourier_smul]
  simp only [Pi.smul_apply, smul_eq_mul, inverseRadianFourier,
    radianFourierIntegral_schwartzConvolution]
  ring

noncomputable def homogeneousYProduct (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) :
    HomogeneousY a k →L[ℂ] HomogeneousY a k →L[ℂ] HomogeneousY a k :=
  (((((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℝ) : ℂ) •
    homogeneousYConvolution a k ha ha1 hk)

theorem homogeneousYProduct_on_Schwartz (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (ψ φ : 𝓢(E, ℂ)) :
    homogeneousYProduct a k ha ha1 hk
      (homogeneousFrequencyEmbedding a k ha ha1 hk ψ)
      (homogeneousFrequencyEmbedding a k ha ha1 hk φ) =
      homogeneousFrequencyEmbedding a k ha ha1 hk
        (((((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℝ) : ℂ) •
          homogeneousSchwartzConvolution ψ φ) := by
  simp only [homogeneousYProduct, smul_apply,
    homogeneousYConvolution_on_Schwartz, map_smul]

/-- Multiplication on Y agrees everywhere with multiplication of the represented functions. -/
theorem homogeneousYProduct_physical (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f g : HomogeneousY a k) (y : E) :
    homogeneousPhysicalCLM a k ha ha1 hk (homogeneousYProduct a k ha ha1 hk f g) y =
      homogeneousPhysicalCLM a k ha ha1 hk f y * homogeneousPhysicalCLM a k ha ha1 hk g y := by
  let P := homogeneousPhysicalCLM a k ha ha1 hk
  let B := homogeneousYProduct a k ha ha1 hk
  have hev : Continuous (fun h : C₀(E, ℂ) => h y) :=
    (BoundedContinuousFunction.evalCLM ℂ y).continuous.comp
      ZeroAtInftyContinuousMap.isometry_toBCF.continuous
  have hleft : Continuous (fun p : HomogeneousY a k × HomogeneousY a k => P (B p.1 p.2) y) :=
    (hev.comp P.continuous).comp ((B.continuous.comp continuous_fst).clm_apply continuous_snd)
  have hright : Continuous (fun p : HomogeneousY a k × HomogeneousY a k => P p.1 y * P p.2 y) :=
    ((hev.comp P.continuous).comp continuous_fst).mul
      ((hev.comp P.continuous).comp continuous_snd)
  have he := ((homogeneousFrequencyEmbedding_dense a k ha ha1 hk).prodMap
    (homogeneousFrequencyEmbedding_dense a k ha ha1 hk)).equalizer hleft hright (by
      funext p
      rcases p with ⟨ψ, φ⟩
      change homogeneousPhysicalCLM a k ha ha1 hk
        (homogeneousYProduct a k ha ha1 hk
          (homogeneousFrequencyEmbedding a k ha ha1 hk ψ)
          (homogeneousFrequencyEmbedding a k ha ha1 hk φ)) y =
        homogeneousPhysicalCLM a k ha ha1 hk (homogeneousFrequencyEmbedding a k ha ha1 hk ψ) y *
          homogeneousPhysicalCLM a k ha ha1 hk (homogeneousFrequencyEmbedding a k ha ha1 hk φ) y
      rw [homogeneousYProduct_on_Schwartz, homogeneousPhysicalCLM_rawSchwartz,
        homogeneousPhysicalCLM_rawSchwartz, homogeneousPhysicalCLM_rawSchwartz]
      exact inverseRadianFourier_normalizedConvolution ψ φ y)
  exact congrFun he (f, g)

end DefocusingNLS

end OAI
