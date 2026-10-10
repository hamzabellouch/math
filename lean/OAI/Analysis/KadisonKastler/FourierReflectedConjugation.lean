import OAI.Analysis.KadisonKastler.RegularReflection
import OAI.Analysis.KadisonKastler.L2FourierNaturality

namespace OAI

/-! # Fourier transform of reflected antiunitary conjugation -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private def conjugationRealMap (J : H ≃ₗᵢ⋆[ℂ] H) : H →L[ℝ] H where
  toFun := J
  map_add' := J.map_add
  map_smul' r x := by
    change J ((r : ℂ) • x) = (r : ℂ) • J x
    simp only [map_smulₛₗ, Complex.conj_ofReal]
  cont := J.continuous

private def reflectedConjugateSchwartz (J : H ≃ₗᵢ⋆[ℂ] H) (f : SchwartzMap ℝ H) :
    SchwartzMap ℝ H :=
  SchwartzMap.postcompCLM (conjugationRealMap J)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (LinearIsometryEquiv.neg ℝ (E := ℝ)) f)

omit [CompleteSpace H] in
private theorem reflectedConjugateSchwartz_apply (J : H ≃ₗᵢ⋆[ℂ] H)
    (f : SchwartzMap ℝ H) (t : ℝ) : reflectedConjugateSchwartz J f t = J (f (-t)) := rfl

omit [CompleteSpace H] in
private theorem reflectedConjugateSchwartz_toLp (J : H ≃ₗᵢ⋆[ℂ] H)
    (f : SchwartzMap ℝ H) :
    (reflectedConjugateSchwartz J f).toLp 2 = regularReflectedConjugation J (f.toLp 2) := by
  apply Lp.ext
  filter_upwards [(reflectedConjugateSchwartz J f).coeFn_toLp 2,
    regularReflectedConjugation_apply_ae J (f.toLp 2),
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq_comp
      (f.coeFn_toLp 2)] with t hg hr hf
  simp only [Function.comp_def] at hf
  rw [hg, hr, hf]
  rfl

private theorem fourier_reflectedConjugateSchwartz (J : H ≃ₗᵢ⋆[ℂ] H)
    (f : SchwartzMap ℝ H) (t : ℝ) :
    (𝓕 (reflectedConjugateSchwartz J f)) t = J ((𝓕 f) t) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, Real.fourier_real_eq,
    Real.fourier_real_eq]
  have hi : Integrable (fun v : ℝ => (Real.fourierChar (-(v*t)) : ℂ) • f v) := by
    simpa only [RCLike.inner_apply, conj_trivial, Circle.smul_def, mul_comm] using
      ((Real.fourierIntegral_convergent_iff t).mpr f.integrable)
  have hj := (conjugationRealMap J).integral_comp_comm hi
  change (∫ v : ℝ, (Real.fourierChar (-(v*t)) : ℂ) •
    reflectedConjugateSchwartz J f v) = J (∫ v : ℝ, (Real.fourierChar (-(v*t)) : ℂ) • f v)
  change (∫ v : ℝ, J ((Real.fourierChar (-(v*t)) : ℂ) • f v)) =
    J (∫ v : ℝ, (Real.fourierChar (-(v*t)) : ℂ) • f v) at hj
  rw [← hj]
  calc
    _ = ∫ v : ℝ, (Real.fourierChar (v * t) : ℂ) • J (f v) := by
      rw [← integral_neg_eq_self]
      apply integral_congr_ae
      filter_upwards [] with v
      simp only [reflectedConjugateSchwartz_apply, neg_mul, neg_neg]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with v
      rw [map_smulₛₗ]
      simp only [Real.fourierChar_apply]
      change _ = (starRingEnd ℂ) (Complex.exp _) • J (f v)
      rw [← Complex.exp_conj]
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
      congr 2
      push_cast
      ring

theorem fourier_regularReflectedConjugation (J : H ≃ₗᵢ⋆[ℂ] H)
    (f : RegularCoreHilbert H) :
    (𝓕 (regularReflectedConjugation J f) : RegularCoreHilbert H) =
      regularPointwiseConjugation J (𝓕 f) := by
  refine (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := H)
    (p := 2) ENNReal.ofNat_ne_top).induction_on
    (p := fun f => (𝓕 (regularReflectedConjugation J f) : RegularCoreHilbert H) =
      regularPointwiseConjugation J (𝓕 f)) f ?_ ?_
  · exact isClosed_eq
      ((Lp.fourierTransformₗᵢ ℝ H).continuous.comp (regularReflectedConjugation J).continuous)
      ((regularPointwiseConjugation J).continuous.comp (Lp.fourierTransformₗᵢ ℝ H).continuous)
  · intro g
    change (𝓕 (regularReflectedConjugation J (g.toLp 2)) : RegularCoreHilbert H) =
      regularPointwiseConjugation J (𝓕 (g.toLp 2))
    rw [← reflectedConjugateSchwartz_toLp, SchwartzMap.toLp_fourier_eq,
      SchwartzMap.toLp_fourier_eq]
    apply Lp.ext
    filter_upwards [(𝓕 (reflectedConjugateSchwartz J g)).coeFn_toLp 2,
      regularPointwiseConjugation_apply_ae J ((𝓕 g).toLp 2),
      (𝓕 g).coeFn_toLp 2] with t hg hj hf
    rw [hg, hj, hf]
    exact fourier_reflectedConjugateSchwartz J g t

end

end KadisonKastler

end OAI
