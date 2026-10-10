import OAI.Analysis.KadisonKastler.StateActionAverages
import OAI.Analysis.KadisonKastler.PureStateExtension
import Mathlib.Analysis.InnerProductSpace.StarOrder

namespace OAI

/-! # States composed with probability averages

Positivity is proved on vectors, so the initial state need not be normal.
-/

namespace KadisonKastler

open MeasureTheory Filter NaimarkZFC
open scoped ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem probabilityOperatorIntegral_positive
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (C : ℝ) (hb : ∀ᵐ t ∂μ, ‖F t‖ ≤ C)
    (hp : ∀ᵐ t ∂μ, (F t).IsPositive) :
    (probabilityOperatorIntegral μ F hm C hb).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro x
  have hi := integrable_bounded_operator_vector μ F hm hb x
  have he : inner ℂ x (probabilityOperatorIntegral μ F hm C hb x) =
      ∫ t, inner ℂ x (F t x) ∂μ := by
    exact ((innerSL ℂ x).integral_comp_comm hi).symm
  have hr : 0 ≤ inner ℂ x (probabilityOperatorIntegral μ F hm C hb x) := by
    rw [he]
    exact integral_nonneg_of_ae (hp.mono fun t ht => ht.inner_nonneg_right x)
  have hl : 0 ≤ inner ℂ (probabilityOperatorIntegral μ F hm C hb x) x := by
    rw [← inner_conj_symm]
    exact star_nonneg_iff.mpr hr
  exact ⟨Complex.ext rfl hl.2,hl.1⟩

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem stateActionAverage_square_positive (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : H →L[ℂ] H) : (stateActionAverage U hU μ (star a*a)).IsPositive := by
  apply probabilityOperatorIntegral_positive
  apply Eventually.of_forall
  intro t
  let e : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H) :=
    Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (U (Multiplicative.ofAdd t))
  have he : e (star a*a)=star (e a)*e a := by
    calc
      _ = e (star a)*e a := e.map_mul _ _
      _ = _ := congrArg (fun b : H →L[ℂ] H => b*e a) (map_star e a)
  change (e (star a*a)).IsPositive
  rw [he]
  exact ContinuousLinearMap.nonneg_iff_isPositive.mp (star_mul_self_nonneg (e a))

theorem state_comp_actionAverage (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : IsState φ) :
    IsState (φ.comp (stateActionAverageMap U hU μ)) := by
  apply (isState_iff _).mpr
  constructor
  · change φ (stateActionAverage U hU μ 1)=1
    rw [stateActionAverage_one]
    exact ((isState_iff φ).mp hφ).1
  · intro a
    have hp := (positiveOfSquares φ hφ.2).map_nonneg
      (ContinuousLinearMap.nonneg_iff_isPositive.mpr
        (stateActionAverage_square_positive U hU μ a))
    exact ⟨hp.2.symm,hp.1⟩

end

end KadisonKastler

end OAI
