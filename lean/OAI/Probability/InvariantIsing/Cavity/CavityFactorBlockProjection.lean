import OAI.Probability.InvariantIsing.Cavity.CavityCompressionFactors

namespace OAI

/-! Extraction of cavity coefficients from the full small compression
matrix. This lets the proved Haar compression law act on the actual
factor coefficients, including the subtracted base diagonal. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

def cavityFactorBlocksFromMatrix {d n : ℕ} (A₀ : Matrix (Fin d) (Fin d) ℝ)
    (M : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) : CavityFactorBlocks d n :=
  (M.submatrix Sum.inl Sum.inl - A₀, M.submatrix Sum.inl Sum.inr,
    M.submatrix Sum.inr Sum.inr)

lemma continuous_cavityFactorBlocksFromMatrix {d n : ℕ}
    (A₀ : Matrix (Fin d) (Fin d) ℝ) : Continuous (cavityFactorBlocksFromMatrix (n := n) A₀) :=
  ((continuous_id.matrix_submatrix _ _).sub continuous_const).prodMk
    ((continuous_id.matrix_submatrix _ _).prodMk (continuous_id.matrix_submatrix _ _))

lemma cavityFactorBlocksFromMatrix_special {s d n : ℕ}
    (D : Matrix (Fin s) (Fin s) ℝ) (A₀ : Matrix (Fin d) (Fin d) ℝ)
    (B : Matrix (Fin s) (Fin d) ℝ) (T : Matrix (Fin s) (Fin n) ℝ) :
    cavityFactorBlocksFromMatrix A₀ (cavitySpecialBlocks D B T) =
      cavitySmallFactorBlocks D A₀ B T := rfl

lemma cavitySmallFactorBlocks_reindex {s d n r : ℕ}
    (e : Fin s ≃ Fin r) (D : Matrix (Fin s) (Fin s) ℝ)
    (A₀ : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin s) (Fin d) ℝ)
    (T : Matrix (Fin s) (Fin n) ℝ) :
    cavitySmallFactorBlocks (D.submatrix e.symm e.symm) A₀
      (B.submatrix e.symm id) (T.submatrix e.symm id) = cavitySmallFactorBlocks D A₀ B T := by
  simp only [cavitySmallFactorBlocks, Matrix.transpose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]

lemma cavityCompressionFactorBlocks_eq_projection {m d n : ℕ}
    (e : Fin (m*n) ≃ Fin (d+n)) (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ)
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
    (M : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    cavityCompressionFactorBlocks e lam lam₀ B₀ M =
      cavityFactorBlocksFromMatrix (Matrix.diagonal lam₀)
        (cavityCompressionBlocks e
          ((cavityRepeatedSpectrum (n := n) lam).submatrix e.symm e.symm) B₀ M) := by
  rw [cavityCompressionFactorBlocks, ← cavitySmallFactorBlocks_reindex e,
    cavityCompressionBlocks, cavityFactorBlocksFromMatrix_special]
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, cavityConcreteComplement, id_eq, Equiv.apply_symm_apply]

end InvariantIsing

end

end OAI
