import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousConvolutionBound

namespace OAI

/-! # Continuous convolution on the faithful homogeneous completion -/

open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousConvolutionPartial (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (ψ : 𝓢(E, ℂ)) :
    HomogeneousY a k →L[ℂ] HomogeneousY a k :=
  ((homogeneousFrequencyEmbedding a k ha ha1 hk).toLinearMap.comp
    ((SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)) ψ).toLinearMap).extendOfNorm
      (homogeneousFrequencyEmbedding a k ha ha1 hk).toLinearMap

theorem homogeneousConvolutionPartial_on_Schwartz (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (ψ φ : 𝓢(E, ℂ)) :
    homogeneousConvolutionPartial a k ha ha1 hk ψ
      (homogeneousFrequencyEmbedding a k ha ha1 hk φ) =
      homogeneousFrequencyEmbedding a k ha ha1 hk (homogeneousSchwartzConvolution ψ φ) := by
  apply LinearMap.extendOfNorm_eq (homogeneousFrequencyEmbedding_dense a k ha ha1 hk)
  exact ⟨homogeneousAlgebraConstant a k * ‖homogeneousFrequencyEmbedding a k ha ha1 hk ψ‖,
    homogeneousSchwartzConvolution_norm_le a k ha ha1 hk ψ⟩

theorem homogeneousConvolutionPartial_norm_le (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (ψ : 𝓢(E, ℂ)) :
    ‖homogeneousConvolutionPartial a k ha ha1 hk ψ‖ ≤
      homogeneousAlgebraConstant a k * ‖homogeneousFrequencyEmbedding a k ha ha1 hk ψ‖ := by
  apply LinearMap.opNorm_extendOfNorm_le (homogeneousFrequencyEmbedding_dense a k ha ha1 hk)
    (mul_nonneg (homogeneousAlgebraConstant_nonneg a k) (norm_nonneg _))
  exact homogeneousSchwartzConvolution_norm_le a k ha ha1 hk ψ

theorem homogeneousConvolutionPartial_add (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (ψ φ : 𝓢(E, ℂ)) :
    homogeneousConvolutionPartial a k ha ha1 hk (ψ + φ) =
      homogeneousConvolutionPartial a k ha ha1 hk ψ +
        homogeneousConvolutionPartial a k ha ha1 hk φ := by
  have he := (homogeneousFrequencyEmbedding_dense a k ha ha1 hk).equalizer
    (homogeneousConvolutionPartial a k ha ha1 hk (ψ + φ)).continuous
    (homogeneousConvolutionPartial a k ha ha1 hk ψ +
      homogeneousConvolutionPartial a k ha ha1 hk φ).continuous (by
      funext χ
      simp only [Function.comp_apply, add_apply,
        homogeneousConvolutionPartial_on_Schwartz, homogeneousSchwartzConvolution,
        map_add])
  apply ContinuousLinearMap.ext
  intro f
  exact congrFun he f

theorem homogeneousConvolutionPartial_smul (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (c : ℂ) (ψ : 𝓢(E, ℂ)) :
    homogeneousConvolutionPartial a k ha ha1 hk (c • ψ) =
      c • homogeneousConvolutionPartial a k ha ha1 hk ψ := by
  have he := (homogeneousFrequencyEmbedding_dense a k ha ha1 hk).equalizer
    (homogeneousConvolutionPartial a k ha ha1 hk (c • ψ)).continuous
    (c • homogeneousConvolutionPartial a k ha ha1 hk ψ).continuous (by
      funext χ
      simp only [Function.comp_apply, smul_apply,
        homogeneousConvolutionPartial_on_Schwartz, homogeneousSchwartzConvolution,
        map_smul])
  apply ContinuousLinearMap.ext
  intro f
  exact congrFun he f

noncomputable def homogeneousConvolutionPartialLinear (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) :
    𝓢(E, ℂ) →ₗ[ℂ] (HomogeneousY a k →L[ℂ] HomogeneousY a k) where
  toFun := homogeneousConvolutionPartial a k ha ha1 hk
  map_add' := homogeneousConvolutionPartial_add a k ha ha1 hk
  map_smul' := homogeneousConvolutionPartial_smul a k ha ha1 hk

/-- The actual continuous-frequency convolution extends to every vector of Y. -/
noncomputable def homogeneousYConvolution (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) :
    HomogeneousY a k →L[ℂ] HomogeneousY a k →L[ℂ] HomogeneousY a k :=
  (homogeneousConvolutionPartialLinear a k ha ha1 hk).extendOfNorm
    (homogeneousFrequencyEmbedding a k ha ha1 hk).toLinearMap

theorem homogeneousYConvolution_on_Schwartz (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (ψ φ : 𝓢(E, ℂ)) :
    homogeneousYConvolution a k ha ha1 hk
      (homogeneousFrequencyEmbedding a k ha ha1 hk ψ)
      (homogeneousFrequencyEmbedding a k ha ha1 hk φ) =
      homogeneousFrequencyEmbedding a k ha ha1 hk (homogeneousSchwartzConvolution ψ φ) := by
  have h := LinearMap.extendOfNorm_eq
    (f := homogeneousConvolutionPartialLinear a k ha ha1 hk)
    (e := (homogeneousFrequencyEmbedding a k ha ha1 hk).toLinearMap)
    (homogeneousFrequencyEmbedding_dense a k ha ha1 hk)
    ⟨homogeneousAlgebraConstant a k, homogeneousConvolutionPartial_norm_le a k ha ha1 hk⟩ ψ
  change ((homogeneousConvolutionPartialLinear a k ha ha1 hk).extendOfNorm
    (homogeneousFrequencyEmbedding a k ha ha1 hk).toLinearMap
      (homogeneousFrequencyEmbedding a k ha ha1 hk ψ)) _ = _
  exact (congrArg (fun T : HomogeneousY a k →L[ℂ] HomogeneousY a k =>
    T (homogeneousFrequencyEmbedding a k ha ha1 hk φ)) h).trans
      (homogeneousConvolutionPartial_on_Schwartz a k ha ha1 hk ψ φ)

theorem homogeneousYConvolution_norm_le (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f g : HomogeneousY a k) :
    ‖homogeneousYConvolution a k ha ha1 hk f g‖ ≤
      homogeneousAlgebraConstant a k * ‖f‖ * ‖g‖ := by
  have h := LinearMap.norm_extendOfNorm_apply_le
    (f := homogeneousConvolutionPartialLinear a k ha ha1 hk)
    (e := (homogeneousFrequencyEmbedding a k ha ha1 hk).toLinearMap)
    (homogeneousFrequencyEmbedding_dense a k ha ha1 hk)
    (homogeneousAlgebraConstant a k) (homogeneousConvolutionPartial_norm_le a k ha ha1 hk) f
  exact (ContinuousLinearMap.le_opNorm _ g).trans
    (mul_le_mul_of_nonneg_right h (norm_nonneg g))

end DefocusingNLS

end OAI
