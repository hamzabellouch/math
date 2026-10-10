import OAI.Analysis.KadisonSimilarity.Tracial.MatrixDiagonalEmbedding
import Mathlib.Data.Matrix.Basis

namespace OAI

/-! # Irreducibility of an entrywise matrix inclusion

The scalar matrix units force any relative commutant element to be a constant
diagonal matrix. Its diagonal entry commutes with the original inclusion,
so scalarity of the original relative commutant proves scalarity after
matrix amplification. No normality or factor classification is used.
-/

noncomputable section
namespace KadisonSimilarity

variable {R B : Type*} [CStarAlgebra R] [CStarAlgebra B] {n : ℕ}

@[simp] theorem matrixEntryHom_single (ρ : R →⋆ₐ[ℂ] B)
    (i j : Fin n) (a : R) :
    matrixEntryHom ρ (CStarMatrix.ofMatrix (Matrix.single i j a)) =
      CStarMatrix.ofMatrix (Matrix.single i j (ρ a)) := by
  ext k l
  simp only [matrixEntryHom_apply, CStarMatrix.ofMatrix_apply, Matrix.single_apply]
  split_ifs <;> simp only [map_zero]

/-- Commutation with all scalar matrix units forces a constant diagonal. -/
theorem matrix_diagonal_of_commutes_units
    (X : CStarMatrix (Fin n) (Fin n) B)
    (hX : ∀ i j : Fin n,
      X * CStarMatrix.ofMatrix (Matrix.single i j (1 : B)) =
        CStarMatrix.ofMatrix (Matrix.single i j (1 : B)) * X) :
    ∃ b : B, X = matrixDiagonalHom n b := by
  let M : Matrix (Fin n) (Fin n) B := CStarMatrix.ofMatrix.symm X
  have hM : Pairwise (fun i j : Fin n => Commute (Matrix.single i j (1 : B)) M) := by
    intro i j _
    have h := congrArg CStarMatrix.ofMatrix.symm (hX i j)
    change M * Matrix.single i j 1 = Matrix.single i j 1 * M at h
    exact h.symm
  obtain ⟨b, hb⟩ := Matrix.mem_range_scalar_of_commute_single hM
  refine ⟨b, ?_⟩
  apply CStarMatrix.ofMatrix.symm.injective
  change M = Matrix.scalar (Fin n) b
  exact hb.symm

variable [NeZero n]

/-- An irreducible inclusion remains irreducible after finite matrix
amplification. Scalars refer to the actual complex algebra maps. -/
theorem scalar_of_matrix_relative_commutant
    (ρ : R →⋆ₐ[ℂ] B)
    (hρ : ∀ b : B, (∀ a : R, b * ρ a = ρ a * b) →
      ∃ z : ℂ, b = algebraMap ℂ B z)
    (X : CStarMatrix (Fin n) (Fin n) B)
    (hX : ∀ Y : CStarMatrix (Fin n) (Fin n) R,
      X * matrixEntryHom ρ Y = matrixEntryHom ρ Y * X) :
    ∃ z : ℂ, X = algebraMap ℂ (CStarMatrix (Fin n) (Fin n) B) z := by
  have hunits i j :
      X * CStarMatrix.ofMatrix (Matrix.single i j (1 : B)) =
        CStarMatrix.ofMatrix (Matrix.single i j (1 : B)) * X := by
    have h := hX (CStarMatrix.ofMatrix (Matrix.single i j (1 : R)))
    simpa only [matrixEntryHom_single, map_one] using h
  obtain ⟨b, hb⟩ := matrix_diagonal_of_commutes_units X hunits
  have hcomm (a : R) : b * ρ a = ρ a * b := by
    have h := hX (matrixDiagonalHom n a)
    rw [matrixEntryHom_diagonal, hb] at h
    apply matrixDiagonalHom_injective n
    simpa only [map_mul] using h
  obtain ⟨z, hz⟩ := hρ b hcomm
  refine ⟨z, ?_⟩
  rw [hb, hz]
  exact (matrixDiagonalHom n).commutes z

end KadisonSimilarity

end

end OAI
