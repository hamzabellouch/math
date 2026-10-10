import OAI.Algebra.DepthFive.TraceComplexification

namespace OAI

noncomputable section
open scoped BigOperators Matrix

namespace Problem335

variable {I J P : Type*} [Fintype I] [Fintype J] [Fintype P]
  [DecidableEq I] [DecidableEq J]

/-- Nonnegative path coefficients suffice for a first-moment lower bound.
Unlike the exact identity, this does not require disjoint path shifts. -/
theorem pathShiftMatrix_first_trace_lower
    (shift : I → P → J) (weight : I → P → ℝ)
    (hw : ∀ i p, 0 ≤ weight i p) :
    (∑ i, ∑ p, weight i p ^ 2) ≤
      Matrix.trace ((pathShiftMatrix shift weight).transpose *
        pathShiftMatrix shift weight) := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, pathShiftMatrix_gram_apply]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro p hp
  have h := Finset.single_le_sum
    (fun q (_ : q ∈ (Finset.univ : Finset P)) =>
      show 0 ≤ (if shift i p = shift i q then weight i p * weight i q else 0) from
        by split_ifs
           · exact mul_nonneg (hw i p) (hw i q)
           · exact le_rfl)
    (Finset.mem_univ p)
  simpa only [ite_true, pow_two] using h

/-- Real nonnegative path coefficients give the same lower bound in the
genuine complex Gram trace. -/
theorem complex_path_first_trace_lower_nonnegative
    (shift : I → P → J) (weight : I → P → ℝ)
    (hw : ∀ i p, 0 ≤ weight i p) :
    let A := pathShiftMatrix shift (fun i p => (weight i p : ℂ))
    (∑ i, ∑ p, weight i p ^ 2) ≤ (A.conjTranspose * A).trace.re := by
  dsimp
  rw [← pathShiftMatrix_complexify, complexify_first_trace]
  exact pathShiftMatrix_first_trace_lower shift weight hw

/-- A uniform source-average path-mass lower bound gives the expected
dimension times path-count lower bound for the complex first trace. -/
theorem complex_path_first_trace_lower_of_average [Nonempty I]
    (shift : I → P → J) (weight : I → P → ℝ) (L : ℝ)
    (hw : ∀ i p, 0 ≤ weight i p)
    (hmean : ∀ p, L ≤ (∑ i, weight i p ^ 2) / (Fintype.card I : ℝ)) :
    let A := pathShiftMatrix shift (fun i p => (weight i p : ℂ))
    (Fintype.card I : ℝ) * (Fintype.card P : ℝ) * L ≤
      (A.conjTranspose * A).trace.re := by
  dsimp
  have hcard : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos
  have hsum : ∀ p, (Fintype.card I : ℝ) * L ≤ ∑ i, weight i p ^ 2 := by
    intro p
    simpa only [mul_comm] using (le_div_iff₀ hcard).mp (hmean p)
  calc
    (Fintype.card I : ℝ) * (Fintype.card P : ℝ) * L =
        ∑ p : P, (Fintype.card I : ℝ) * L := by simp; ring
    _ ≤ ∑ p : P, ∑ i : I, weight i p ^ 2 :=
      Finset.sum_le_sum (fun p _ => hsum p)
    _ = ∑ i : I, ∑ p : P, weight i p ^ 2 := Finset.sum_comm
    _ ≤ _ := complex_path_first_trace_lower_nonnegative shift weight hw

end Problem335

end

end OAI
