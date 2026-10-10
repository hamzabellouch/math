import OAI.Analysis.ModularTheory.ScalarCompression
import Mathlib.Analysis.Fourier.LpSpace

namespace OAI

/-! Fourier diagonalization of the regular translations in the concrete
modular representation. The normalization is the Mathlib convention with
the factor 2π. No spectral or trace property of the core is assumed. -/

noncomputable section
open MeasureTheory FourierTransform
open scoped SchwartzMap

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
private lemma fourier_schwartz_translation (s : ℝ) (f : 𝓢(ℝ, H)) (w : ℝ) :
    (𝓕 (f.compSubConstCLM ℂ s)) w =
      BoundedRecovery.spectralCharacter (-2 * Real.pi * s) w • (𝓕 f) w := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar (volume : Measure ℝ) (innerₗ ℝ) (f : ℝ → H) (-s)) w
  have hc : (Real.fourierChar ((innerₗ ℝ) (-s) w) : ℂ) =
      BoundedRecovery.spectralCharacter (-2 * Real.pi * s) w := by
    simp only [Real.fourierChar_apply, innerₗ_apply_apply, RCLike.inner_apply, conj_trivial]
    dsimp [BoundedRecovery.spectralCharacter]
    congr 2
    ring_nf
  have hg : (f.compSubConstCLM ℂ s : ℝ → H) = (f : ℝ → H) ∘ (fun v => v + -s) := by
    ext v
    simp only [SchwartzMap.compSubConstCLM_apply, Function.comp_apply, sub_eq_add_neg]
  change VectorFourier.fourierIntegral Real.fourierChar (volume : Measure ℝ)
    (innerₗ ℝ) (f.compSubConstCLM ℂ s : ℝ → H) w =
      BoundedRecovery.spectralCharacter (-2 * Real.pi * s) w •
        VectorFourier.fourierIntegral Real.fourierChar (volume : Measure ℝ)
          (innerₗ ℝ) (f : ℝ → H) w
  rw [hg]
  simpa only [Circle.smul_def, hc] using h

omit [CompleteSpace H] in
private lemma modularLpTranslate_schwartz (s : ℝ) (f : 𝓢(ℝ, H)) :
    modularLpTranslate (volume : Measure ℝ) s (f.toLp 2) =
      (f.compSubConstCLM ℂ s).toLp 2 := by
  apply Lp.ext
  filter_upwards [modularLpTranslate_ae (volume : Measure ℝ) s (f.toLp 2),
    (measurePreserving_sub_right (volume : Measure ℝ) s).quasiMeasurePreserving.ae
      (f.coeFn_toLp 2 (volume : Measure ℝ)),
    (f.compSubConstCLM ℂ s).coeFn_toLp 2 (volume : Measure ℝ)] with t ht hf hg
  rw [ht, hf, hg, SchwartzMap.compSubConstCLM_apply]

private lemma fourier_modularLpTranslate_schwartz (s : ℝ) (f : 𝓢(ℝ, H)) :
    𝓕 (modularLpTranslate (volume : Measure ℝ) s (f.toLp 2)) =
      modularDual (volume : Measure ℝ) (-2 * Real.pi * s) (𝓕 (f.toLp 2)) := by
  rw [modularLpTranslate_schwartz, SchwartzMap.toLp_fourier_eq,
    SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (f.compSubConstCLM ℂ s)).coeFn_toLp 2 (volume : Measure ℝ),
    modularDual_ae (volume : Measure ℝ) (-2 * Real.pi * s) ((𝓕 f).toLp 2),
    (𝓕 f).coeFn_toLp 2 (volume : Measure ℝ)] with w hl hr hf
  rw [hl, hr, hf, fourier_schwartz_translation]

/-- The actual L² Fourier unitary diagonalizes every regular translation. -/
theorem fourier_modularLpTranslate (s : ℝ) (f : Lp H 2 (volume : Measure ℝ)) :
    𝓕 (modularLpTranslate (volume : Measure ℝ) s f) =
      modularDual (volume : Measure ℝ) (-2 * Real.pi * s) (𝓕 f) := by
  have hd : DenseRange (SchwartzMap.toLpCLM ℝ H 2 (volume : Measure ℝ)) :=
    SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  apply hd.induction_on (p := fun g =>
    𝓕 (modularLpTranslate (volume : Measure ℝ) s g) =
      modularDual (volume : Measure ℝ) (-2 * Real.pi * s) (𝓕 g)) f
  · exact isClosed_eq
      ((Lp.fourierTransformₗᵢ ℝ H).continuous.comp
        (modularLpTranslate (volume : Measure ℝ) s).continuous)
      ((modularDualUnitary (volume : Measure ℝ) (-2 * Real.pi * s)).continuous.comp
        (Lp.fourierTransformₗᵢ ℝ H).continuous)
  · intro g
    exact fourier_modularLpTranslate_schwartz s g

end WeakPureInfiniteness

end

end OAI
