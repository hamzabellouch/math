import OAI.Analysis.KadisonKastler.PositiveFrequencyAlgebra
import OAI.Analysis.KadisonKastler.RegularCoreActions

namespace OAI

/-! # Constant operators commute with the Fourier frequency cuts -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem constantSchwartz_toLp (T : H →L[ℂ] H) (f : SchwartzMap ℝ H) :
    (f.postcompCLM T).toLp 2 = regularConstantOperator volume T (f.toLp 2) := by
  apply Lp.ext
  filter_upwards [(f.postcompCLM T).coeFn_toLp 2,
    regularConstantOperator_apply_ae volume T (f.toLp 2), f.coeFn_toLp 2]
    with t h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  rfl

private theorem fourier_constant_schwartz (T : H →L[ℂ] H) (f : SchwartzMap ℝ H) :
    (𝓕 (regularConstantOperator volume T (f.toLp 2)) : RegularCoreHilbert H) =
      regularConstantOperator volume T (𝓕 (f.toLp 2)) := by
  rw [← constantSchwartz_toLp, SchwartzMap.toLp_fourier_eq,
    SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (f.postcompCLM T)).coeFn_toLp 2,
    regularConstantOperator_apply_ae volume T ((𝓕 f).toLp 2),
    (𝓕 f).coeFn_toLp 2] with t h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  change (𝓕 (fun s => T (f s))) t = T (𝓕 (f : ℝ → H) t)
  simp only [Real.fourier_eq]
  rw [← T.integral_comp_comm ((Real.fourierIntegral_convergent_iff t).mpr f.integrable)]
  congr 1
  funext s
  exact (T.map_smul _ _).symm

theorem fourier_regularConstantOperator (T : H →L[ℂ] H) (f : RegularCoreHilbert H) :
    (𝓕 (regularConstantOperator volume T f) : RegularCoreHilbert H) =
      regularConstantOperator volume T (𝓕 f) := by
  let F : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H := Lp.fourierTransformₗᵢ ℝ H
  let C : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H := regularConstantOperator volume T
  have he : F.comp C = C.comp F := by
    apply DFunLike.coe_injective
    apply (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := H)
      (p := 2) ENNReal.ofNat_ne_top).equalizer (F.comp C).continuous (C.comp F).continuous
    funext g
    exact fourier_constant_schwartz T g
  exact congrArg (fun A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => A f) he

theorem regularConstantOperator_commutes_frequency (T : H →L[ℂ] H) (a : ℝ) :
    Commute (regularConstantOperator volume T) (regularFrequencyProjection a) := by
  apply ContinuousLinearMap.ext
  intro f
  apply (Lp.fourierTransformₗᵢ ℝ H).injective
  change (𝓕 (regularConstantOperator volume T (regularFrequencyProjection a f)) :
    RegularCoreHilbert H) = 𝓕 (regularFrequencyProjection a (regularConstantOperator volume T f))
  rw [fourier_regularConstantOperator]
  apply Lp.ext
  have hp := regularFrequencyProjection_apply_fourier a (regularConstantOperator volume T f)
  rw [fourier_regularConstantOperator] at hp
  filter_upwards [regularConstantOperator_apply_ae volume T (𝓕 (regularFrequencyProjection a f)),
    regularFrequencyProjection_apply_fourier a f, hp,
    regularConstantOperator_apply_ae volume T (𝓕 f)] with t hc hf hg ht
  rw [hc, hg, hf]
  by_cases hmem : t ∈ Set.Ioi (a / (2 * Real.pi))
  · simp only [Set.indicator_of_mem hmem, ht]
  · simp only [Set.indicator_of_notMem hmem, map_zero]

theorem regularConstantOperator_mem_positiveFrequencyAlgebra (T : H →L[ℂ] H) :
    regularConstantOperator volume T ∈ positiveFrequencyAlgebra (H := H) := by
  refine ⟨fun s => (regularCharacter_commute_constant s T).symm, ?_⟩
  rw [← (regularConstantOperator_commutes_frequency T 0).eq, mul_assoc,
    (regularFrequencyProjection_isStarProjection (H := H) 0).isIdempotentElem.eq]

end

end KadisonKastler

end OAI
