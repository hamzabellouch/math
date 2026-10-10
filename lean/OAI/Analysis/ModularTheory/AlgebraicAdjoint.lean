import OAI.Analysis.ModularTheory.AlgebraicNormalForm

namespace OAI

/-! Adjoint-weight symmetry for Gaussian regularizations of algebraic
core elements, with arbitrary finite-weight translation multipliers. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma modularTranslationCalculus_translate (t : ℝ) :
    modularTranslationCalculus (H := H) (spectralCharacter (-2 * Real.pi * t)) =
      (modularLpTranslateEquiv (H := H) volume t :
        Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) := by
  rw [modularTranslationCalculus_character]
  congr 1
  field_simp [Real.pi_ne_zero]

theorem modularAlgebraic_regularized_adjoint_weight (S : StandardModularData H)
    (P : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hP : P ∈ algebraicModularCore (volume : Measure ℝ) S)
    (g : BoundedContinuousFunction ℝ ℂ)
    (hg : Integrable (fun ω : ℝ => ‖g ω‖ ^ 2 * Real.exp (2 * Real.pi * ω))) :
    modularCoreSquareWeight S (star (P * modularTranslationCalculus g)) =
      modularCoreSquareWeight S (P * modularTranslationCalculus g) := by
  classical
  obtain ⟨c, hc⟩ := algebraicModularCore_normal_form S P hP
  let a (p : S.M.toStarSubalgebra × ℝ) : H →L[ℂ] H := c p • (p.1 : H →L[ℂ] H)
  let k (p : S.M.toStarSubalgebra × ℝ) : BoundedContinuousFunction ℝ ℂ :=
    spectralCharacter (-2 * Real.pi * p.2) * g
  have he : P * modularTranslationCalculus g =
      ∑ p ∈ c.support, modularLpRepresentation volume S.D (a p) *
        modularTranslationCalculus (k p) := by
    rw [← hc]
    simp only [Finsupp.sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    dsimp [a, k, modularCoreMonomial]
    rw [map_mul, modularTranslationCalculus_translate, map_smul]
    simp only [smul_mul_assoc, mul_assoc]
  rw [he]
  apply modularFiniteNormalOrdered_adjoint_weight S c.support a k
  · intro p _
    exact S.M.toStarSubalgebra.smul_mem p.1.property (c p)
  · intro p _
    simpa only [k, BoundedContinuousFunction.coe_mul, Pi.mul_apply,
      norm_mul, spectralCharacter_norm, one_mul] using hg

end WeakPureInfiniteness

end

end OAI
