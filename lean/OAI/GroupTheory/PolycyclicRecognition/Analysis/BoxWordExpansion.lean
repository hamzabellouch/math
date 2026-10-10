import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledWordSums

namespace OAI

/-! # Finite word coefficients of an actual enlarged box point -/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators

/-- Membership in a scaled word box supplies a finite expansion with a
common coefficient bound. Repetitions are harmless; the dimension factor
also covers them without any uniqueness requirement. -/
theorem exists_word_expansion_of_rescaled_norm_le
    {I L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (cost : S → ℝ) (r : ℝ) {R : ℝ} (hR : 0 ≤ R) (v : L)
    (hv : ‖(exponentialRescaleBasis (WordBasisSelections.basis X S β)
      (fun i => cost (β.val i)) r).equivFun v‖ ≤ R) :
    ∃ a : S → ℝ,
      (∀ w, |a w| ≤ (finrank ℝ L : ℝ) * R * Real.exp (r * cost w)) ∧
      ∑ w, a w • evalBracketWord X w = v := by
  classical
  let b := exponentialRescaleBasis (WordBasisSelections.basis X S β)
    (fun i => cost (β.val i)) r
  let a : S → ℝ := fun w => ∑ i : Fin (finrank ℝ L),
    if β.val i = w then Real.exp (r * cost w) * b.repr v i else 0
  refine ⟨a, ?_, ?_⟩
  · intro w
    have hb (i : Fin (finrank ℝ L)) : |b.repr v i| ≤ R :=
      (norm_le_pi_norm (b.equivFun v) i).trans hv
    have hi (i : Fin (finrank ℝ L)) :
        |if β.val i = w then Real.exp (r * cost w) * b.repr v i else 0| ≤
          R * Real.exp (r * cost w) := by
      split_ifs
      · rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
        exact mul_le_mul_of_nonneg_right (hb i) (Real.exp_pos _).le
      · simp only [abs_zero]
        positivity
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact (Finset.sum_le_sum (fun i _ => hi i)).trans_eq (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring)
  · calc
      (∑ w, a w • evalBracketWord X w) =
          ∑ i : Fin (finrank ℝ L),
            (Real.exp (r * cost (β.val i)) * b.repr v i) •
              evalBracketWord X (β.val i) := by
        simp only [a, Finset.sum_smul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        simp
      _ = ∑ i, b.repr v i • b i := by
        apply Finset.sum_congr rfl
        intro i _
        have hw := WordBasisSelections.eval_words X S β i
        change evalBracketWord X (β.val i) = _ at hw
        rw [hw]
        simp only [b, exponentialRescaleBasis, Basis.unitsSMul_apply,
          Units.smul_def, Units.val_mk0, smul_smul]
        rw [mul_comm]
      _ = v := b.sum_repr v

/-- The deterministic enlarged suffix has precisely the coefficient
envelope used by interior slack. Its subexponential radius is retained. -/
theorem exists_word_expansion_of_enlarged_box
    {I L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (X : I → L) (S : Finset (FreeMagma I)) (β : WordBasisSelections X S)
    (cost : S → ℝ) (r δ ε : ℝ) (v : L)
    (hv : ‖(exponentialRescaleBasis (WordBasisSelections.basis X S β)
      (fun i => (1 + δ) * cost (β.val i)) r).equivFun v‖ ≤ Real.exp (r * ε)) :
    ∃ a : S → ℝ,
      (∀ w, |a w| ≤ (finrank ℝ L : ℝ) *
        Real.exp (r * ((1 + δ) * cost w + ε))) ∧
      ∑ w, a w • evalBracketWord X w = v := by
  obtain ⟨a, ha, he⟩ := exists_word_expansion_of_rescaled_norm_le X S β
    (fun w => (1 + δ) * cost w) r (Real.exp_pos _).le v hv
  refine ⟨a, fun w => (ha w).trans_eq ?_, he⟩
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

end PolycyclicRecognition

end

end OAI
