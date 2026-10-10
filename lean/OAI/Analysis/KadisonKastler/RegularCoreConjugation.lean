import OAI.Analysis.KadisonKastler.RegularReflection

namespace OAI

/-! # The antiunitary of the regular modular representation

In concrete coordinates this sends `f(t)` to `U(-t) J(f(-t))`.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (J : H ≃ₗᵢ⋆[ℂ] H)

def regularCoreConjugation : RegularCoreHilbert H ≃ₗᵢ⋆[ℂ] RegularCoreHilbert H :=
  (regularReflectedConjugation J).trans
    (Unitary.linearIsometryEquiv (star (regularGauge U hU)))

theorem regularCoreConjugation_apply_ae (f : RegularCoreHilbert H) :
    regularCoreConjugation U hU J f =ᵐ[volume] fun t =>
      (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) (J (f (-t))) := by
  filter_upwards [regularGauge_star_apply_ae U hU (regularReflectedConjugation J f),
    regularReflectedConjugation_apply_ae J f] with t hg hr
  exact hg.trans (congrArg (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) hr)

theorem regularCoreConjugation_involutive (hJ : Function.Involutive J)
    (hJU : ∀ t x, J ((U t : H →L[ℂ] H) x) = (U t : H →L[ℂ] H) (J x)) :
    Function.Involutive (regularCoreConjugation U hU J) := by
  intro f
  apply Lp.ext
  filter_upwards [regularCoreConjugation_apply_ae U hU J (regularCoreConjugation U hU J f),
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq_comp
      (regularCoreConjugation_apply_ae U hU J f)] with t ho hi
  simp only [Function.comp_def, neg_neg] at hi
  rw [ho, hi]
  simp only [← Unitary.coe_star, regularGroup_star_eq U (-t), neg_neg]
  rw [hJU, hJ]
  exact congrArg (fun A : H →L[ℂ] H => A (f t))
    (Unitary.star_mul_self_of_mem (U (Multiplicative.ofAdd t)).property)

end

end KadisonKastler

end OAI
