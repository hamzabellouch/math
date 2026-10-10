import OAI.Analysis.ModularTheory.FiniteTrace

namespace OAI

/-! Faithful normalized traces on the positive-size finite core corners. -/

noncomputable section
open MeasureTheory
open scoped CStarAlgebra ComplexOrder ENNReal

namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma modularFiniteCornerFunctional_faithful (S : StandardModularData H) (n : ℕ)
    (a : ModularFiniteCorner S n)
    (ha : modularFiniteCornerFunctional S n (star a * a) = 0) : a = 0 := by
  have hn : ‖modularFiniteCornerRepresentation S n a (modularCoreWeightVector S n)‖ ^ 2 = 0 := by
    rw [modularFiniteCornerFunctional_square] at ha
    exact_mod_cast ha
  have hw : modularCoreSquareWeight S (modularFiniteCornerRepresentation S n a) = 0 := by
    rw [modularCore_finite_corner_weight S n _ (modularFiniteCornerRepresentation_mem S n a)
      (modularFiniteCornerRepresentation_right S n a), hn, ENNReal.ofReal_zero]
  have hz := (modularCoreSquareWeight_eq_zero_iff S _
    (modularFiniteCornerRepresentation_mem S n a)).mp hw
  apply Subtype.ext
  apply Subtype.ext
  exact hz

def modularFiniteCornerNormalizedFunctional (S : StandardModularData H) (n : ℕ) :
    ModularFiniteCorner S (n + 1) →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    ((‖modularCoreWeightVector S (n + 1)‖ ^ 2 : ℝ)⁻¹ •
      (modularFiniteCornerFunctional S (n + 1)).toLinearMap)
    (fun a ha => mul_nonneg
      (show (0 : ℂ) ≤ ((‖modularCoreWeightVector S (n + 1)‖ ^ 2 : ℝ)⁻¹ : ℝ) from
        by exact_mod_cast inv_nonneg.mpr (sq_nonneg _))
      ((modularFiniteCornerFunctional S (n + 1)).map_nonneg ha))

lemma modularFiniteCornerNormalizedFunctional_apply (S : StandardModularData H) (n : ℕ)
    (a : ModularFiniteCorner S (n + 1)) :
    modularFiniteCornerNormalizedFunctional S n a =
      ((‖modularCoreWeightVector S (n + 1)‖ ^ 2 : ℝ)⁻¹ : ℝ) *
        modularFiniteCornerFunctional S (n + 1) a := rfl

def modularFiniteCornerTracialState (S : StandardModularData H) (n : ℕ) :
    Pureness.TracialState (ModularFiniteCorner S (n + 1)) where
  functional := modularFiniteCornerNormalizedFunctional S n
  normalized := by
    rw [modularFiniteCornerNormalizedFunctional_apply, modularFiniteCornerFunctional_one]
    have hn : ‖modularCoreWeightVector S (n + 1)‖ ^ 2 ≠ 0 :=
      ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr (modularCoreWeightVector_succ_ne_zero S n)))
    exact_mod_cast inv_mul_cancel₀ hn
  tracial a b := by
    simp only [modularFiniteCornerNormalizedFunctional_apply,
      modularFiniteCornerFunctional_tracial S (n + 1) a b]

theorem modularFiniteCornerTracialState_faithful (S : StandardModularData H) (n : ℕ)
    (a : ModularFiniteCorner S (n + 1))
    (ha : (modularFiniteCornerTracialState S n).functional (star a * a) = 0) : a = 0 := by
  apply modularFiniteCornerFunctional_faithful S (n + 1) a
  change (((‖modularCoreWeightVector S (n + 1)‖ ^ 2 : ℝ)⁻¹ : ℝ) : ℂ) *
    modularFiniteCornerFunctional S (n + 1) (star a * a) = 0 at ha
  apply (mul_eq_zero.mp ha).resolve_left
  exact_mod_cast (inv_ne_zero (ne_of_gt (sq_pos_of_pos
    (norm_pos_iff.mpr (modularCoreWeightVector_succ_ne_zero S n)))))

end WeakPureInfiniteness

end

end OAI
