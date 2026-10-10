import OAI.Analysis.ModularTheory.WeightFaithful

namespace OAI

/-! The faithful extended quadratic weight defined by modular cutoff vectors,
with its exact null space. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : BoundedRecovery.StandardModularData H)

def modularCoreSquareWeight
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (‖T (modularCoreWeightVector S n)‖ ^ 2)

lemma modularCoreCutoffFunctional_square (n : ℕ)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) :
    modularCoreCutoffFunctional S n (star T * T) =
      (‖T (modularCoreWeightVector S n)‖ ^ 2 : ℝ) := by
  change inner ℂ (modularCoreWeightVector S n)
    (star T (T (modularCoreWeightVector S n))) = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  norm_cast

@[simp] lemma modularCoreSquareWeight_zero : modularCoreSquareWeight S 0 = 0 := by
  simp [modularCoreSquareWeight]

lemma modularCoreSquareWeight_eq_zero_iff
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : T ∈ modularCrossedProduct (volume : Measure ℝ) S) :
    modularCoreSquareWeight S T = 0 ↔ T = 0 := by
  constructor
  · intro hz
    apply modularCoreCutoffs_faithful_square S T hT
    intro n
    have hn : ENNReal.ofReal (‖T (modularCoreWeightVector S n)‖ ^ 2) = 0 :=
      le_zero_iff.mp ((le_iSup (fun n : ℕ =>
        ENNReal.ofReal (‖T (modularCoreWeightVector S n)‖ ^ 2)) n).trans_eq hz)
    have hr : ‖T (modularCoreWeightVector S n)‖ ^ 2 = 0 :=
      le_antisymm (ENNReal.ofReal_eq_zero.mp hn) (sq_nonneg _)
    rw [modularCoreCutoffFunctional_square, hr, Complex.ofReal_zero]
  · rintro rfl
    exact modularCoreSquareWeight_zero S

lemma modularCoreSquareWeight_mul_le
    (R T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) :
    modularCoreSquareWeight S (R * T) ≤
      ENNReal.ofReal (‖R‖ ^ 2) * modularCoreSquareWeight S T := by
  apply iSup_le
  intro n
  have h : ‖(R * T) (modularCoreWeightVector S n)‖ ^ 2 ≤
      ‖R‖ ^ 2 * ‖T (modularCoreWeightVector S n)‖ ^ 2 := by
    change ‖R (T (modularCoreWeightVector S n))‖ ^ 2 ≤ _
    calc
      _ ≤ (‖R‖ * ‖T (modularCoreWeightVector S n)‖) ^ 2 := by
        gcongr
        exact R.le_opNorm _
      _ = _ := mul_pow _ _ _
  calc
    ENNReal.ofReal _ ≤ ENNReal.ofReal
        (‖R‖ ^ 2 * ‖T (modularCoreWeightVector S n)‖ ^ 2) := ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal (‖R‖ ^ 2) *
        ENNReal.ofReal (‖T (modularCoreWeightVector S n)‖ ^ 2) :=
      ENNReal.ofReal_mul (sq_nonneg _)
    _ ≤ _ := by
      gcongr
      exact le_iSup (fun k : ℕ => ENNReal.ofReal (‖T (modularCoreWeightVector S k)‖ ^ 2)) n

lemma modularCoreSquareWeight_add_le
    (R T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)) :
    modularCoreSquareWeight S (R + T) ≤
      2 * (modularCoreSquareWeight S R + modularCoreSquareWeight S T) := by
  apply iSup_le
  intro n
  have h : ‖(R + T) (modularCoreWeightVector S n)‖ ^ 2 ≤
      2 * (‖R (modularCoreWeightVector S n)‖ ^ 2 +
        ‖T (modularCoreWeightVector S n)‖ ^ 2) := by
    have h₁ := norm_add_le (R (modularCoreWeightVector S n))
      (T (modularCoreWeightVector S n))
    have h₂ := sq_nonneg (‖R (modularCoreWeightVector S n)‖ -
      ‖T (modularCoreWeightVector S n)‖)
    change ‖R (modularCoreWeightVector S n) + T (modularCoreWeightVector S n)‖ ^ 2 ≤ _
    nlinarith [norm_nonneg (R (modularCoreWeightVector S n) + T (modularCoreWeightVector S n)),
      norm_nonneg (R (modularCoreWeightVector S n)), norm_nonneg (T (modularCoreWeightVector S n))]
  calc
    ENNReal.ofReal _ ≤ ENNReal.ofReal
        (2 * (‖R (modularCoreWeightVector S n)‖ ^ 2 +
          ‖T (modularCoreWeightVector S n)‖ ^ 2)) := ENNReal.ofReal_le_ofReal h
    _ = 2 * (ENNReal.ofReal (‖R (modularCoreWeightVector S n)‖ ^ 2) +
        ENNReal.ofReal (‖T (modularCoreWeightVector S n)‖ ^ 2)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
      norm_num
    _ ≤ _ := by
      gcongr
      · exact le_iSup (fun k : ℕ => ENNReal.ofReal (‖R (modularCoreWeightVector S k)‖ ^ 2)) n
      · exact le_iSup (fun k : ℕ => ENNReal.ofReal (‖T (modularCoreWeightVector S k)‖ ^ 2)) n

end WeakPureInfiniteness

end

end OAI
