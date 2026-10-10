import OAI.Analysis.KadisonKastler.RegularPointwiseConjugation

namespace OAI

/-! # Reflection and conjugation on the real regular representation -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def regularReflectionApply (f : RegularCoreHilbert H) : RegularCoreHilbert H :=
  Lp.compMeasurePreserving (fun t : ℝ => -t) (Measure.measurePreserving_neg volume) f

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem regularReflectionApply_ae (f : RegularCoreHilbert H) :
    regularReflectionApply f =ᵐ[volume] fun t => f (-t) :=
  Lp.coeFn_compMeasurePreserving f (Measure.measurePreserving_neg volume)

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem regularReflectionApply_involutive :
    Function.Involutive (regularReflectionApply (H := H)) := by
  intro f
  apply Lp.ext
  filter_upwards [regularReflectionApply_ae (regularReflectionApply f),
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq_comp
      (regularReflectionApply_ae f)] with t houter hinner
  simp only [Function.comp_def, neg_neg] at hinner
  rw [houter, hinner]

def regularReflection : RegularCoreHilbert H ≃ₗᵢ[ℂ] RegularCoreHilbert H where
  __ := Lp.compMeasurePreservingₗᵢ ℂ (fun t : ℝ => -t)
    (Measure.measurePreserving_neg volume)
  invFun := regularReflectionApply
  left_inv := regularReflectionApply_involutive
  right_inv := regularReflectionApply_involutive

def regularReflectedConjugation (J : H ≃ₗᵢ⋆[ℂ] H) :
    RegularCoreHilbert H ≃ₗᵢ⋆[ℂ] RegularCoreHilbert H :=
  regularReflection.trans (regularPointwiseConjugation J)

omit [CompleteSpace H] in
theorem regularReflectedConjugation_apply_ae (J : H ≃ₗᵢ⋆[ℂ] H)
    (f : RegularCoreHilbert H) :
    regularReflectedConjugation J f =ᵐ[volume] fun t => J (f (-t)) := by
  filter_upwards [regularPointwiseConjugation_apply_ae J (regularReflection f),
    regularReflectionApply_ae f] with t hj hr
  exact hj.trans (congrArg J hr)

omit [CompleteSpace H] in
theorem regularReflectedConjugation_involutive (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) : Function.Involutive (regularReflectedConjugation J) := by
  intro f
  apply Lp.ext
  filter_upwards [regularReflectedConjugation_apply_ae J (regularReflectedConjugation J f),
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq_comp
      (regularReflectedConjugation_apply_ae J f)] with t ho hi
  simp only [Function.comp_def, neg_neg] at hi
  rw [ho, hi, hJ]

end

end KadisonKastler

end OAI
