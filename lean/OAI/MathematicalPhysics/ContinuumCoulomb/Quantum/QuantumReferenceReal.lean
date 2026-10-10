import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumReferenceHistory
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliMonomial

namespace OAI

/-! Distributed reference terms are actual real Hermitian matrices. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem qmaLocalY_real_zero (n : ℕ) (i : Fin n) (s t : SourceSpinBasis n) :
    (sourceLocalPauli n i 1 s t).re = 0 := by
  rw [qmaLocalPauli_monomial]
  simp only [qmaPauliPhase,Fin.isValue,ite_true]
  split_ifs <;> simp

omit [Fintype α] [DecidableEq α] in
theorem qmaDistributedRebitTerm_real (n : ℕ) (i : Fin n) (A : Matrix α α ℂ)
    (p q : SourceSpinBasis n × α) : (qmaDistributedRebitTerm n i A p q).im = 0 := by
  rcases p with ⟨s,a⟩
  rcases q with ⟨t,b⟩
  simp only [qmaDistributedRebitTerm,Matrix.add_apply,Matrix.kronecker_apply,
    Matrix.smul_apply,smul_eq_mul,qmaEntryReal,qmaEntryImag,Complex.add_im,
    Complex.mul_im,Complex.mul_re,Complex.ofReal_im,Complex.ofReal_re,
    qmaLocalY_real_zero,zero_mul,mul_zero,add_zero,sub_zero]
  simp only [Matrix.one_apply]
  split_ifs <;> simp

theorem qmaHermitian_of_conjugated {β : Type*} [Fintype β] [DecidableEq β]
    (B M : Matrix β β ℂ) (hB : B*B.conjTranspose = 1)
    (hM : (B.conjTranspose*M*B).IsHermitian) : M.IsHermitian := by
  have he : B*(B.conjTranspose*M*B)*B.conjTranspose = M := by
    calc
      _ = (B*B.conjTranspose)*M*(B*B.conjTranspose) := by simp only [mul_assoc]
      _ = M := by rw [hB]; simp
  rw [←he]
  exact Matrix.isHermitian_mul_mul_conjTranspose B hM

omit [Fintype α] [DecidableEq α] in
theorem qmaConjugateMatrix_hermitian (A : Matrix α α ℂ) (hA : A.IsHermitian) :
    (qmaConjugateMatrix A).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro a b
  exact congrArg star (hA.apply a b)

omit [Fintype α] [DecidableEq α] in
theorem qmaReferenceBlocks_hermitian (n : ℕ) (A : SourceSpinBasis n → Matrix α α ℂ)
    (hA : ∀ s, (A s).IsHermitian) : (qmaReferenceBlocks n A).IsHermitian := by
  apply Matrix.IsHermitian.ext
  rintro ⟨s,a⟩ ⟨t,b⟩
  by_cases hs : s = t
  · subst t
    simpa only [qmaReferenceBlocks,ite_true] using (hA s).apply a b
  · simp [qmaReferenceBlocks,hs,Ne.symm hs]

theorem qmaDistributedRebitTerm_hermitian (n : ℕ) (i : Fin n) (A : Matrix α α ℂ)
    (hA : A.IsHermitian) : (qmaDistributedRebitTerm n i A).IsHermitian := by
  apply qmaHermitian_of_conjugated (qmaReferenceExtension (α := α) n) _
    (qmaReferenceExtension_cogram n)
  rw [qmaDistributedRebitTerm_blocks]
  apply qmaReferenceBlocks_hermitian
  intro s
  unfold qmaReferenceSectorTerm
  split_ifs
  · exact qmaConjugateMatrix_hermitian A hA
  · exact hA

theorem qmaReferenceYPenalty_hermitian (n : ℕ) : (qmaReferenceYPenalty n).IsHermitian := by
  apply qmaHermitian_of_conjugated (qmaReferenceTensor (n+1)) _
    (qmaReferenceTensor_cogram _)
  rw [qmaReferenceYPenalty_diagonalized]
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro s
  simp [isSelfAdjoint_iff]

omit [Fintype α] in
theorem qmaReferenceFamily_real (n : ℕ) (A : Fin (n+1) → Matrix α α ℂ) (Δ : ℝ)
    (p q : SourceSpinBasis (n+1) × α) : (qmaReferenceFamily n A Δ p q).im = 0 := by
  rcases p with ⟨s,a⟩
  rcases q with ⟨t,b⟩
  simp only [qmaReferenceFamily,Matrix.add_apply,Matrix.sum_apply,Complex.add_im,
    Complex.im_sum,qmaDistributedRebitTerm_real,Finset.sum_const_zero,zero_add,
    Matrix.smul_apply,smul_eq_mul,Matrix.kronecker_apply,Complex.mul_im,
    Complex.ofReal_im,Complex.ofReal_re,zero_mul,add_zero,qmaReferenceYPenalty_real]
  simp only [Matrix.one_apply]
  split_ifs <;> simp

theorem qmaReferenceFamily_hermitian (n : ℕ) (A : Fin (n+1) → Matrix α α ℂ) (Δ : ℝ)
    (hA : ∀ i, (A i).IsHermitian) : (qmaReferenceFamily n A Δ).IsHermitian := by
  unfold qmaReferenceFamily
  apply Matrix.IsHermitian.add
  · apply Matrix.IsHermitian.ext
    intro p q
    simp only [Matrix.sum_apply,star_sum]
    exact Finset.sum_congr rfl (fun i _ =>
      (qmaDistributedRebitTerm_hermitian _ _ _ (hA i)).apply p q)
  · have hp : (qmaReferenceYPenalty n ⊗ₖ (1 : Matrix α α ℂ)).IsHermitian := by
      simp only [Matrix.IsHermitian,Matrix.conjTranspose_kronecker,
        (qmaReferenceYPenalty_hermitian n).eq,Matrix.conjTranspose_one]
    exact hp.smul (by simp [isSelfAdjoint_iff])

end ContinuumCoulomb

end

end OAI
