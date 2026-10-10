import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumReferencePenalty

namespace OAI

/-! Each complex term uses its own local Y reference; uniform sectors recover it exactly. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Kronecker Classical
variable {α : Type*} [Fintype α] [DecidableEq α]

def qmaDistributedRebitTerm (n : ℕ) (i : Fin n) (A : Matrix α α ℂ) :
    Matrix (SourceSpinBasis n × α) (SourceSpinBasis n × α) ℂ :=
  (1 : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) ⊗ₖ qmaEntryReal A +
    (-Complex.I) • (sourceLocalPauli n i 1 ⊗ₖ qmaEntryImag A)

def qmaReferenceExtension (n : ℕ) :
    Matrix (SourceSpinBasis n × α) (SourceSpinBasis n × α) ℂ :=
  qmaReferenceTensor n ⊗ₖ (1 : Matrix α α ℂ)

theorem qmaDistributedRebitTerm_diagonalized (n : ℕ) (i : Fin n) (A : Matrix α α ℂ) :
    (qmaReferenceExtension (α := α) n).conjTranspose*qmaDistributedRebitTerm n i A*
      qmaReferenceExtension (α := α) n =
    (1 : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) ⊗ₖ qmaEntryReal A +
      (-Complex.I) • (sourceLocalPauli n i 2 ⊗ₖ qmaEntryImag A) := by
  unfold qmaReferenceExtension qmaDistributedRebitTerm
  rw [Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,Matrix.mul_add,Matrix.add_mul,
    mul_smul_comm,smul_mul_assoc]
  simp only [←Matrix.mul_kronecker_mul,mul_one,one_mul,qmaReferenceTensor_gram,
    qmaReferenceTensor_y]

theorem qmaDistributedRebitTerm_block (n : ℕ) (i : Fin n) (A : Matrix α α ℂ)
    (s t : SourceSpinBasis n) (a b : α) :
    ((qmaReferenceExtension (α := α) n).conjTranspose*qmaDistributedRebitTerm n i A*
      qmaReferenceExtension (α := α) n) (s,a) (t,b) =
    if s = t then (if s i = 0 then star (A a b) else A a b) else 0 := by
  rw [qmaDistributedRebitTerm_diagonalized,sourceLocalPauli_z_diagonal]
  by_cases h : s = t
  · subst t
    simp only [Matrix.add_apply,Matrix.kronecker_apply,Matrix.one_apply_eq,
      Matrix.diagonal_apply_eq,Matrix.smul_apply,smul_eq_mul,one_mul,qmaEntryReal,qmaEntryImag]
    simp only [ite_true]
    generalize hb : s i = c
    fin_cases c <;> apply Complex.ext <;> simp [qmaZSign,Complex.mul_re,Complex.mul_im]
  · simp [Matrix.add_apply,h]

end ContinuumCoulomb

end

end OAI
