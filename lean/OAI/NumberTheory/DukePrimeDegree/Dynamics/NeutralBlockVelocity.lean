import OAI.NumberTheory.DukePrimeDegree.Dynamics.MatrixExponentialVelocity
import OAI.NumberTheory.DukePrimeDegree.Dynamics.VelocityRootProjection
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Trace

namespace OAI

/-!
# Actual neutral block directions in the measure stabilizer

Full diagonal invariance and invariance under the roots within equal-weight
blocks give every trace-zero neutral matrix as the derivative of a curve
in the actual stabilizer. Exponential recovery then gives its entire
one-parameter group. This is only the neutral-group input: it does not
construct a singular parabolic chart or an atomic conditional graph.
-/

noncomputable section
open Matrix MeasureTheory Set
open scoped BigOperators Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma hasIdentityMatrixDerivative_diagonalOneParameter {n : ℕ}
    (v : Fin n → ℝ) (hv : ∑ i, v i = 0) :
    HasIdentityMatrixDerivative (diagonalOneParameter v hv) (Matrix.diagonal v) := by
  refine ⟨diagonalOneParameter_zero v hv, ?_⟩
  intro i j
  by_cases hij : i = j
  · subst j
    change HasDerivAt (fun t =>
      (Matrix.diagonal (fun a => Real.exp (v a * t))) i i) (Matrix.diagonal v i i) 0
    simp only [Matrix.diagonal_apply_eq]
    convert ((hasDerivAt_id (0 : ℝ)).const_mul (v i)).exp using 1 <;> simp
  · change HasDerivAt (fun t =>
      (Matrix.diagonal (fun a => Real.exp (v a * t))) i j) (Matrix.diagonal v i j) 0
    simp only [Matrix.diagonal_apply_ne _ hij]
    exact hasDerivAt_const _ _

/-- All neutral infinitesimal directions arise from actual subgroup
curves; a Lie algebra is not assigned as an additional hypothesis. -/
theorem neutral_matrix_mem_velocitySpace {n : ℕ}
    (ell : Fin n → ℝ) (L : Subgroup (G n))
    (hdiag : ∀ (v : Fin n → ℝ) (hv : ∑ i, v i = 0) (t : ℝ),
      diagonalOneParameter v hv t ∈ L)
    (hroot : ∀ (i j : Fin n) (hij : i ≠ j), ell i = ell j →
      ∀ t : ℝ, SpecialLinearGroup.transvection hij t ∈ L)
    (V : Matrix (Fin n) (Fin n) ℝ) (htrace : Matrix.trace V = 0)
    (hneutral : ∀ i j, ell i ≠ ell j → V i j = 0) :
    V ∈ matrixVelocitySpace L := by
  let D := Matrix.diagonal (fun i => V i i)
  have hsum : ∑ i, V i i = 0 := htrace
  have hD : D ∈ matrixVelocitySpace L :=
    ⟨diagonalOneParameter (fun i => V i i) hsum,
      hdiag _ hsum, hasIdentityMatrixDerivative_diagonalOneParameter _ hsum⟩
  have hoff : V - D ∈ matrixVelocitySpace L := by
    rw [Matrix.matrix_eq_sum_single (V - D)]
    apply (matrixVelocitySpace L).sum_mem
    intro i _
    apply (matrixVelocitySpace L).sum_mem
    intro j _
    by_cases hij : i = j
    · subst j
      simp only [Matrix.sub_apply, D, Matrix.diagonal_apply_eq, sub_self,
        Matrix.single_zero]
      exact (matrixVelocitySpace L).zero_mem
    · by_cases he : ell i = ell j
      · exact ⟨fun t => SpecialLinearGroup.transvection hij (t * (V - D) i j),
          fun t => hroot i j hij he _,
          hasIdentityMatrixDerivative_rootCurve hij ((V - D) i j)⟩
      · have hz : (V - D) i j = 0 := by
          simp only [Matrix.sub_apply, hneutral i j he, D,
            Matrix.diagonal_apply_ne _ hij, sub_zero]
        rw [hz, Matrix.single_zero]
        exact (matrixVelocitySpace L).zero_mem
  have h := (matrixVelocitySpace L).add_mem hD hoff
  rw [show D + (V - D) = V by abel] at h
  exact h

/-- The infinitesimal support condition really is neutrality for the
chosen singular diagonal flow. -/
lemma neutral_matrix_conjugation_fixed {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (V : Matrix (Fin n) (Fin n) ℝ)
    (hneutral : ∀ i j, ell i ≠ ell j → V i j = 0) (t : ℝ) :
    (diagonalOneParameter ell hell t).val * V *
      (diagonalOneParameter ell hell (-t)).val = V := by
  ext i j
  rw [diagonal_matrix_conjugation_entry]
  by_cases he : ell i = ell j
  · simp only [he, sub_self, zero_mul, Real.exp_zero, one_mul]
  · rw [hneutral i j he, mul_zero]

theorem neutral_matrix_exp_mem_stabilizer {n : ℕ} [Nonempty (Fin n)]
    (ell : Fin n → ℝ) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hdiag : ∀ (v : Fin n → ℝ) (hv : ∑ i, v i = 0) (t : ℝ),
      μ.map (fun x => rightAction x (diagonalOneParameter v hv t)) = μ)
    (hroot : ∀ (i j : Fin n) (hij : i ≠ j), ell i = ell j →
      ∀ t : ℝ, μ.map (fun x => rightAction x
        (SpecialLinearGroup.transvection hij t)) = μ)
    (V : Matrix (Fin n) (Fin n) ℝ) (htrace : Matrix.trace V = 0)
    (hneutral : ∀ i j, ell i ≠ ell j → V i j = 0) (t : ℝ) :
    ∃ g : G n, μ.map (fun x => rightAction x g) = μ ∧
      g.val = NormedSpace.exp (t • V) := by
  have hV := neutral_matrix_mem_velocitySpace ell (invariantRightSubgroup μ)
    hdiag hroot V htrace hneutral
  exact (mem_matrixVelocitySpace_iff_exp (invariantRightSubgroup μ)
    (isClosed_invariantRightSubgroup μ) V).mp hV t

end DukePrimeDegree

end

end OAI
