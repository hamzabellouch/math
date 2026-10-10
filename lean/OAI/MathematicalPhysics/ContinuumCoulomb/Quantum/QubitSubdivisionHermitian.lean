import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitSubdivisionReal

namespace OAI

/-! Each real subdivision summand is Hermitian, as needed for its next Pauli expansion. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {ι κ α : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype α]

theorem qmaPolarizedFlip_star (m : κ → Bool) (e : κ) :
    (qmaPolarizedFlip m e).conjTranspose = qmaPolarizedFlip m e := by
  rw [← qmaPhaseMatrix_flip]
  exact (Matrix.isHermitian_conjTranspose_mul_mul (qmaPhaseMatrix m)
    (show (qmaBitFlipMatrix e).IsHermitian from qmaBitFlipMatrix_star e)).eq

omit [Fintype ι] [DecidableEq ι] in
theorem qmaJoinMatrix_star (M : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (N : Matrix (κ → Fin 2) (κ → Fin 2) ℂ)
    (hM : M.conjTranspose = M) (hN : N.conjTranspose = N) :
    (qmaJoinMatrix M N).conjTranspose = qmaJoinMatrix M N := by
  simp only [qmaJoinMatrix,Matrix.conjTranspose_submatrix,Matrix.conjTranspose_kronecker,hM,hN]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem qmaMatrix_real_smul_star {σ : Type*} (M : Matrix σ σ ℂ) (r : ℝ)
    (hM : M.conjTranspose = M) : (r • M).conjTranspose = r • M := by
  rw [Matrix.conjTranspose_smul,star_trivial,hM]

omit [Fintype α] [DecidableEq ι] in
theorem qmaSubdivisionLocalPiece_star (A B : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (e : κ) (R j : ℝ) (m : κ → Bool)
    (hA : A.conjTranspose = A) (hB : B.conjTranspose = B) (k : Fin 4) :
    (qmaSubdivisionLocalPiece A B e R j m k).conjTranspose =
      qmaSubdivisionLocalPiece A B e R j m k := by
  fin_cases k
  · exact qmaMatrix_real_smul_star _ _ (qmaJoinMatrix_star _ _
      Matrix.conjTranspose_one (qmaAncillaOccupation_star e))
  · exact qmaMatrix_real_smul_star _ _ Matrix.conjTranspose_one
  · exact qmaMatrix_real_smul_star _ _ (qmaJoinMatrix_star _ _ hA (qmaPolarizedFlip_star m e))
  · exact qmaMatrix_real_smul_star _ _ (qmaJoinMatrix_star _ _ hB (qmaPolarizedFlip_star m e))

omit [Fintype α] [DecidableEq ι] in
theorem qmaSubdivisionLocalFamily_star (F : α → Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (A B : κ → Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (R : ℝ) (J : κ → ℝ) (m : κ → Bool)
    (hF : ∀ a, (F a).conjTranspose = F a)
    (hA : ∀ e, (A e).conjTranspose = A e) (hB : ∀ e, (B e).conjTranspose = B e)
    (a : α ⊕ (κ × Fin 4)) :
    (qmaSubdivisionLocalFamily F A B R J m a).conjTranspose = qmaSubdivisionLocalFamily F A B R J m a := by
  cases a with
  | inl a => exact qmaJoinMatrix_star _ _ (hF a) Matrix.conjTranspose_one
  | inr p => exact qmaSubdivisionLocalPiece_star _ _ _ _ _ _ (hA p.1) (hB p.1) p.2

end ContinuumCoulomb

end

end OAI
