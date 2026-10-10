import OAI.NumberTheory.Ostmann.ZeroDensity.RieszMellinInversion
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothVerticalKernel

namespace OAI

/-! # The absolutely convergent Riesz contour weight -/

namespace Ostmann

open Complex MeasureTheory

noncomputable def rieszMellinLine (σ t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * I

@[simp] theorem rieszMellinLine_re (σ t : ℝ) : (rieszMellinLine σ t).re = σ := by
  simp [rieszMellinLine]

@[fun_prop] theorem rieszMellinLine_continuous (σ : ℝ) : Continuous (rieszMellinLine σ) := by
  unfold rieszMellinLine
  fun_prop

theorem rieszMellinKernel_analyticAt_pos (s : ℂ) (hs : 0 < s.re) :
    AnalyticAt ℂ rieszMellinKernel s := by
  apply analyticAt_const.div (analyticAt_id.mul (analyticAt_id.add analyticAt_const))
  apply mul_ne_zero
  · intro h
    change s = 0 at h
    simp [h] at hs
  · intro h
    change s + 1 = 0 at h
    have hh := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hh
    linarith

noncomputable def rieszVerticalWeight (X σ t : ℝ) : ℂ :=
  (X : ℂ) ^ rieszMellinLine σ t * rieszMellinKernel (rieszMellinLine σ t)

theorem rieszVerticalWeight_continuous (X σ : ℝ) (hX : 0 < X) (hσ : 0 < σ) :
    Continuous (rieszVerticalWeight X σ) := by
  apply Continuous.mul
  · exact (rieszMellinLine_continuous σ).const_cpow (.inl (by exact_mod_cast hX.ne'))
  · apply continuous_iff_continuousAt.mpr
    intro t
    exact ((rieszMellinKernel_analyticAt_pos _ (by simpa using hσ)).continuousAt).comp
      (rieszMellinLine_continuous σ).continuousAt

theorem rieszVerticalWeight_norm (X σ t : ℝ) (hX : 0 < X) :
    ‖rieszVerticalWeight X σ t‖ = X ^ σ * ‖rieszMellinKernel (rieszMellinLine σ t)‖ := by
  rw [rieszVerticalWeight, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX,
    rieszMellinLine_re]

theorem rieszVerticalWeight_integrable (X σ : ℝ) (hX : 0 < X) (hσ : 1 ≤ σ) :
    Integrable (rieszVerticalWeight X σ) := by
  have hk : Integrable (fun t => rieszMellinKernel (rieszMellinLine σ t)) :=
    rieszMellinKernel_verticalIntegrable σ hσ
  apply (hk.norm.const_mul (X ^ σ)).mono'
    (rieszVerticalWeight_continuous X σ hX (by linarith)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => (rieszVerticalWeight_norm X σ t hX).le)

theorem characterMangoldt_riesz_term_norm (χ : PrimitiveComplexCharacter)
    (σ t : ℝ) (n : ℕ) :
    ‖LSeries.term (characterMangoldtCoefficient χ) (rieszMellinLine σ t) n‖ =
      ‖LSeries.term (characterMangoldtCoefficient χ) (σ : ℂ) n‖ := by
  simp [LSeries.norm_term_eq]

theorem characterMangoldt_riesz_term_continuous (χ : PrimitiveComplexCharacter)
    (σ : ℝ) (n : ℕ) :
    Continuous (fun t => LSeries.term (characterMangoldtCoefficient χ) (rieszMellinLine σ t) n) := by
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero]
    exact continuous_const
  · simp only [LSeries.term_of_ne_zero hn]
    exact continuous_const.div ((rieszMellinLine_continuous σ).const_cpow
      (.inl (by exact_mod_cast hn))) (fun _ => Complex.cpow_ne_zero_iff.mpr
        (.inl (by exact_mod_cast hn)))

end Ostmann

end OAI
