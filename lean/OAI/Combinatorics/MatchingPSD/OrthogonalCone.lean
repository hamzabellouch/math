import Mathlib
import OAI.Combinatorics.MatchingPSD.DiagonalCone

namespace OAI

namespace AffinePSD
open Matrix Finset
open scoped BigOperators
variable {I R : Type*} [Fintype I] [Fintype R] [DecidableEq R]

lemma trace_orthogonal_congruence (U A D : Matrix R R ℝ)
    (hU : U * Uᵀ = 1) :
    ((Uᵀ * A * U) * (Uᵀ * D * U)).trace = (A * D).trace := by
  have he : (Uᵀ * A * U) * (Uᵀ * D * U) = Uᵀ * (A * D) * U := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᵀ, hU, Matrix.one_mul]
  rw [he, Matrix.trace_mul_cycle, hU, Matrix.one_mul]

omit [Fintype I] in
lemma evaluationCone_orthogonal (B : I → Matrix R R ℝ)
    (U : Matrix R R ℝ) (hU' : U * Uᵀ = 1) :
    evaluationCone (fun i => Uᵀ * B i * U) = evaluationCone B := by
  ext y
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨U * A * Uᵀ, ?_, ?_⟩
    · simpa using hA.mul_mul_conjTranspose_same U
    · ext i
      change (U * A * Uᵀ * B i).trace = (A * (Uᵀ * B i * U)).trace
      rw [Matrix.mul_assoc U A Uᵀ, Matrix.mul_assoc U (A * Uᵀ) (B i),
        Matrix.trace_mul_comm U]
      simp only [Matrix.mul_assoc]
  · rintro ⟨A, hA, rfl⟩
    refine ⟨Uᵀ * A * U, ?_, ?_⟩
    · simpa using hA.conjTranspose_mul_mul_same U
    · ext i
      exact trace_orthogonal_congruence U A (B i) hU'

lemma evaluationCone_isClosed (B : I → Matrix R R ℝ)
    (hB : ∀ i, (B i).PosSemidef) : IsClosed (evaluationCone B) := by
  classical
  have hS : (∑ i, B i).PosSemidef := Matrix.posSemidef_sum _ (fun i _ => hB i)
  let U : Matrix R R ℝ := hS.isHermitian.eigenvectorUnitary
  let d : R → ℝ := hS.isHermitian.eigenvalues
  have hU : Uᵀ * U = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hS.isHermitian.eigenvectorUnitary.property.1
  have hU' : U * Uᵀ = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hS.isHermitian.eigenvectorUnitary.property.2
  have hspec : ∑ i, B i = U * diagonal d * Uᵀ := by
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, U, d] using hS.isHermitian.spectral_theorem
  rw [← evaluationCone_orthogonal B U hU']
  refine evaluationCone_isClosed_of_diagonal _ (fun i => ?_) d ?_
  · simpa using (hB i).conjTranspose_mul_mul_same U
  · rw [← Matrix.sum_mul, ← Matrix.mul_sum, hspec]
    simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]
    rw [Matrix.mul_assoc, hU, Matrix.mul_one]

end AffinePSD

end OAI
