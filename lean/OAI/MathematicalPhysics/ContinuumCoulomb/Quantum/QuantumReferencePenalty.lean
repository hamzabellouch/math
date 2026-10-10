import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumDiagonalTensor

namespace OAI

/-! The actual nearest-neighbor real YY penalty has a unit complement gap. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaReferenceYPenalty (n : ℕ) :
    Matrix (SourceSpinBasis (n+1)) (SourceSpinBasis (n+1)) ℂ :=
  ∑ i : Fin n, (1/2 : ℂ) • (1-sourceLocalPauli (n+1) i.castSucc 1*
    sourceLocalPauli (n+1) i.succ 1)

theorem qmaReferenceYEdge_diagonalized (n : ℕ) (i j : Fin n) :
    (qmaReferenceTensor n).conjTranspose*
      ((1/2 : ℂ) • (1-sourceLocalPauli n i 1*sourceLocalPauli n j 1))*
        qmaReferenceTensor n =
    (1/2 : ℂ) • (1-sourceLocalPauli n i 2*sourceLocalPauli n j 2) := by
  rw [mul_smul_comm,smul_mul_assoc,Matrix.mul_sub,Matrix.sub_mul,mul_one,
    qmaReferenceTensor_gram,qmaReferenceTensor_yy]

theorem qmaReferenceYPenalty_diagonalized (n : ℕ) :
    (qmaReferenceTensor (n+1)).conjTranspose*qmaReferenceYPenalty n*
      qmaReferenceTensor (n+1) = qmaReferenceWallMatrix n := by
  unfold qmaReferenceYPenalty
  rw [Matrix.mul_sum,Matrix.sum_mul]
  simp_rw [qmaReferenceYEdge_diagonalized]
  exact qmaReferenceZPenalty_diagonal n

theorem qmaQuadratic_change_basis {α β : Type*} [Fintype α] [Fintype β]
    (B : Matrix α β ℂ) (M : Matrix α α ℂ) (u : β → ℂ) :
    qmaQuadratic (B.conjTranspose*M*B) u = qmaQuadratic M (B.mulVec u) := by
  unfold qmaQuadratic
  rw [Matrix.star_mulVec,←Matrix.dotProduct_mulVec,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec]

theorem qmaReferenceYPenalty_gap (n : ℕ) (u : SourceSpinBasis (n+1) → ℂ) :
    (∑ s, if ∀ i, s i = s 0 then 0 else Complex.normSq (u s)) ≤
      qmaQuadratic (qmaReferenceYPenalty n) ((qmaReferenceTensor (n+1)).mulVec u) := by
  rw [←qmaQuadratic_change_basis,qmaReferenceYPenalty_diagonalized]
  exact qmaReferenceWallMatrix_gap n u

theorem sourcePauli_yy_real (n : ℕ) (i j : Fin n) (hij : i ≠ j)
    (s t : SourceSpinBasis n) : ((sourceLocalPauli n i 1*sourceLocalPauli n j 1) s t).im = 0 := by
  have hY (a b c d : Fin 2) : (pauli 1 a b*pauli 1 c d).im = 0 := by
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      norm_num [pauli,pauliY]
  rw [sourceLocalPauli_product_entry n i j hij]
  by_cases hs : ∀ k, k ≠ i → k ≠ j → s k = t k
  · rw [sourceSpectatorDelta_eq_one n i j s t hs,mul_one]
    exact hY _ _ _ _
  · rw [sourceSpectatorDelta_eq_zero n i j s t hs,mul_zero]
    rfl

theorem qmaReferenceYPenalty_real (n : ℕ) (s t : SourceSpinBasis (n+1)) :
    (qmaReferenceYPenalty n s t).im = 0 := by
  have hne (i : Fin n) : i.castSucc ≠ i.succ := by
    intro he
    have hv := congrArg Fin.val he
    simp at hv
  simp only [qmaReferenceYPenalty,Matrix.sum_apply,Complex.im_sum]
  apply Finset.sum_eq_zero
  intro i _
  simp only [Matrix.smul_apply,smul_eq_mul,Complex.mul_im,Matrix.sub_apply,Complex.sub_im,
    sourcePauli_yy_real _ _ _ (hne i),Matrix.one_apply]
  split_ifs <;> norm_num

end ContinuumCoulomb

end

end OAI
