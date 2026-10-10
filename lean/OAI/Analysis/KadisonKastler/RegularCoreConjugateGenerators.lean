import OAI.Analysis.KadisonKastler.RegularCoreConjugation
import OAI.Analysis.KadisonKastler.ConjugateRightAlgebra

namespace OAI

/-! # Conjugation of the regular generators

The regular modular conjugation sends the represented algebra to the
constant right algebra. Its formula is proved on actual L2 classes.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (J : H ≃ₗᵢ⋆[ℂ] H)
  (hJU : ∀ t x, J ((U t : H →L[ℂ] H) x) = (U t : H →L[ℂ] H) (J x))

private theorem unitary_star_apply_apply (v : unitary (H →L[ℂ] H)) (x : H) :
    (star v : H →L[ℂ] H) ((v : H →L[ℂ] H) x) = x :=
  congrArg (fun A : H →L[ℂ] H => A x) (Unitary.star_mul_self_of_mem v.property)

include hJU in
theorem regularCoreConjugation_embedding (a : H →L[ℂ] H) :
    conjugationOperator (regularCoreConjugation U hU J) (regularCoreEmbedding U hU a) =
      regularConstantHom volume (conjugationOperator J a) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularCoreConjugation_apply_ae U hU J
      (regularCoreEmbedding U hU a (regularCoreConjugation U hU J f)),
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq_comp
      (regularCoreEmbedding_apply_ae U hU a (regularCoreConjugation U hU J f)),
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq_comp
      (regularCoreConjugation_apply_ae U hU J f),
    regularConstantHom_apply_ae volume (conjugationOperator J a) f]
    with t ho ha hc hr
  simp only [Function.comp_def, neg_neg] at ha hc
  change (regularCoreConjugation U hU J
    (regularCoreEmbedding U hU a (regularCoreConjugation U hU J f))) t = _
  have hneg (x : H) : (U (Multiplicative.ofAdd (-t)) : H →L[ℂ] H)
      ((U (Multiplicative.ofAdd t) : H →L[ℂ] H) x) = x := by
    simpa only [← Unitary.coe_star, regularGroup_star_eq] using
      unitary_star_apply_apply (U (Multiplicative.ofAdd t)) x
  rw [ho, ha, hc]
  simp only [← Unitary.coe_star, regularGroup_star_eq U (-t), neg_neg]
  rw [hneg, hJU]
  simp only [Unitary.coe_star]
  rw [unitary_star_apply_apply, hr]
  rfl

include hJU in
theorem regularCoreConjugation_translation (hJ : Function.Involutive J) (s : ℝ) :
    conjugationOperator (regularCoreConjugation U hU J)
      (regularRightTranslation (H := H) (Multiplicative.ofAdd s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (regularCoreAction U (Multiplicative.ofAdd (-s)) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  have hshift : MeasurePreserving (fun t : ℝ => -t + s) volume volume :=
    (measurePreserving_add_right volume s).comp (Measure.measurePreserving_neg volume)
  have hproduct (t : ℝ) :
      (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) *
        (U (Multiplicative.ofAdd (-(-t + s))) : H →L[ℂ] H) =
      (U (Multiplicative.ofAdd (-s)) : H →L[ℂ] H) := by
    have he : U (Multiplicative.ofAdd (-t)) * U (Multiplicative.ofAdd (-(-t + s))) =
        U (Multiplicative.ofAdd (-s)) := by
      rw [← map_mul]
      congr 1
      change -t + -(-t + s) = -s
      ring
    simp only [← Unitary.coe_star, regularGroup_star_eq]
    exact congrArg Subtype.val he
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularCoreConjugation_apply_ae U hU J
      ((regularRightTranslation (H := H) (Multiplicative.ofAdd s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (regularCoreConjugation U hU J f)),
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq_comp
      (regularRightTranslation_apply_ae (Multiplicative.ofAdd s)
        (regularCoreConjugation U hU J f)),
    hshift.quasiMeasurePreserving.ae_eq_comp (regularCoreConjugation_apply_ae U hU J f),
    regularCoreAction_apply_ae U (Multiplicative.ofAdd (-s)) f]
    with t ho ht hc hr
  simp only [Function.comp_def, toAdd_ofAdd] at ht hc hr
  change (regularCoreConjugation U hU J
    ((regularRightTranslation (H := H) (Multiplicative.ofAdd s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (regularCoreConjugation U hU J f))) t = _
  rw [ho, ht, hc]
  simp only [← Unitary.coe_star, regularGroup_star_eq U (-t + s)]
  rw [hJU, hJ, hr]
  change ((star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) *
    (U (Multiplicative.ofAdd (-(-t + s))) : H →L[ℂ] H)) (f (-(-t + s))) = _
  rw [hproduct]
  congr 2
  ring

end

end KadisonKastler

end OAI
