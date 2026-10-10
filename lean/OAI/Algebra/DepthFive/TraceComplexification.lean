import OAI.Algebra.DepthFive.TraceExpansion

namespace OAI

/-! The real nonnegative path matrix can be read over the complex numbers
without changing either of its two trace moments. -/

noncomputable section
open scoped BigOperators Matrix

namespace Problem335

variable {I J P : Type*} [Fintype I] [Fintype J] [Fintype P]
  [DecidableEq I] [DecidableEq J]

/-- Real entrywise complexification sends the real Gram matrix to the complex Gram matrix. -/
theorem complexify_gram {I : Type u_1} {J : Type u_2}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (A : Matrix J I ℝ) :
    (A.map Complex.ofReal).conjTranspose * A.map Complex.ofReal =
      (A.transpose * A).map Complex.ofReal := by
  ext i k
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply,
    Complex.ofReal_sum, Complex.ofReal_mul]

/-- Entrywise complexification preserves the real part of the trace. -/
theorem trace_complexify_re {I : Type u_1} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) :
    (A.map Complex.ofReal).trace.re = A.trace := by
  simp [Matrix.trace, Matrix.map_apply]

/-- First moment agrees over the real and complex coefficient fields. -/
theorem complexify_first_trace (A : Matrix J I ℝ) :
    ((A.map Complex.ofReal).conjTranspose * A.map Complex.ofReal).trace.re =
      (A.transpose * A).trace := by
  rw [complexify_gram, trace_complexify_re]

/-- Second moment agrees over the real and complex coefficient fields. -/
theorem complexify_second_trace (A : Matrix J I ℝ) :
    (((A.map Complex.ofReal).conjTranspose * A.map Complex.ofReal) ^ 2).trace.re =
      ((A.transpose * A) ^ 2).trace := by
  rw [complexify_gram]
  have h : ((A.transpose * A).map Complex.ofReal) ^ 2 =
      ((A.transpose * A) ^ 2).map Complex.ofReal := by
    exact (Matrix.map_pow (A.transpose * A) Complex.ofRealHom 2).symm
  rw [h, trace_complexify_re]

/-- Complexifying a path matrix complexifies just its weights. -/
theorem pathShiftMatrix_complexify {I : Type u_1} {J : Type u_2} {P : Type u_3}
    [Fintype I] [Fintype J] [Fintype P] [DecidableEq I] [DecidableEq J]
    (shift : I → P → J) (weight : I → P → ℝ) :
    (pathShiftMatrix shift weight).map Complex.ofReal =
      pathShiftMatrix shift (fun i p => (weight i p : ℂ)) := by
  ext j i
  simp only [pathShiftMatrix, Matrix.map_apply, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp

/-- First complex trace of the square-root mass path matrix. -/
theorem complex_path_first_trace_sqrt
    (shift : I → P → J) (mass : I → P → ℝ)
    (hnonneg : ∀ i p, 0 ≤ mass i p)
    (hdisjoint : ∀ i p q, p ≠ q → shift i p = shift i q →
      mass i p = 0 ∨ mass i q = 0) :
    let A := pathShiftMatrix shift (fun i p => (Real.sqrt (mass i p) : ℂ))
    (A.conjTranspose * A).trace.re = ∑ i, ∑ p, mass i p := by
  dsimp
  rw [← pathShiftMatrix_complexify, complexify_first_trace]
  exact pathShiftMatrix_first_trace_sqrt shift mass hnonneg hdisjoint

/-- Four-path expression of the second complex trace for real path weights. -/
theorem complex_path_second_trace_four_paths
    (shift : I → P → J) (weight : I → P → ℝ) :
    let A := pathShiftMatrix shift (fun i p => (weight i p : ℂ))
    ((A.conjTranspose * A) ^ 2).trace.re =
      ∑ i, ∑ k, ∑ p, ∑ q, ∑ r, ∑ s,
        if shift i p = shift k q ∧ shift i r = shift k s then
          weight i p * weight k q * weight i r * weight k s else 0 := by
  dsimp
  rw [← pathShiftMatrix_complexify, complexify_second_trace]
  exact pathShiftMatrix_second_trace_four_paths shift weight

end Problem335

end

end OAI
