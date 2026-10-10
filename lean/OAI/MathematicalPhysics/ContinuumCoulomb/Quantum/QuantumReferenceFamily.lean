import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumReferenceBlocks

namespace OAI

/-! The complete distributed reference Hamiltonian and its exact sector matrices. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {α : Type*} [Fintype α] [DecidableEq α]

def qmaReferenceFamily (n : ℕ) (A : Fin (n+1) → Matrix α α ℂ) (Δ : ℝ) :
    Matrix (SourceSpinBasis (n+1) × α) (SourceSpinBasis (n+1) × α) ℂ :=
  (∑ i, qmaDistributedRebitTerm (n+1) i (A i))+
    (Δ:ℂ) • (qmaReferenceYPenalty n ⊗ₖ (1 : Matrix α α ℂ))

def qmaReferenceSector (n : ℕ) (A : Fin (n+1) → Matrix α α ℂ)
    (Δ : ℝ) (s : SourceSpinBasis (n+1)) : Matrix α α ℂ :=
  (∑ i, qmaReferenceSectorTerm (n+1) i (A i) s)+
    ((Δ:ℂ)*(qmaReferenceWalls n s:ℂ)) • 1

theorem qmaReferenceFamily_diagonalized (n : ℕ) (A : Fin (n+1) → Matrix α α ℂ) (Δ : ℝ) :
    (qmaReferenceExtension (α := α) (n+1)).conjTranspose*qmaReferenceFamily n A Δ*
      qmaReferenceExtension (α := α) (n+1) =
    qmaReferenceBlocks (n+1) (qmaReferenceSector n A Δ) := by
  unfold qmaReferenceFamily
  rw [Matrix.mul_add,Matrix.add_mul,Matrix.mul_sum,Matrix.sum_mul,mul_smul_comm,smul_mul_assoc]
  simp_rw [qmaDistributedRebitTerm_blocks]
  rw [qmaReferencePenalty_blocks]
  rw [←qmaReferenceBlocks_sum]
  ext ⟨s,a⟩ ⟨t,b⟩
  by_cases hs : s = t <;>
    simp [qmaReferenceBlocks,qmaReferenceSector,hs,mul_assoc]

omit [Fintype α] in
theorem qmaReferenceSector_one (n : ℕ) (A : Fin (n+1) → Matrix α α ℂ) (Δ : ℝ) :
    qmaReferenceSector n A Δ (fun _ => 1) = ∑ i, A i := by
  simp [qmaReferenceSector,qmaReferenceWalls_constant,qmaReferenceSectorTerm]

omit [Fintype α] in
theorem qmaReferenceSector_zero (n : ℕ) (A : Fin (n+1) → Matrix α α ℂ) (Δ : ℝ) :
    qmaReferenceSector n A Δ (fun _ => 0) = qmaConjugateMatrix (∑ i, A i) := by
  ext a b
  simp [qmaReferenceSector,qmaReferenceWalls_constant,qmaReferenceSectorTerm,qmaConjugateMatrix,Matrix.sum_apply]

omit [DecidableEq α] in
theorem qmaConjugate_quadratic (A : Matrix α α ℂ) (u : α → ℂ) :
    qmaQuadratic (qmaConjugateMatrix A) u = qmaQuadratic A (fun a => star (u a)) := by
  unfold qmaConjugateMatrix
  have he : star u ⬝ᵥ Matrix.mulVec (fun a b => star (A a b)) u =
      star (star (fun a => star (u a)) ⬝ᵥ A.mulVec (fun a => star (u a))) := by
    simp [dotProduct,Matrix.mulVec]
  unfold qmaQuadratic
  rw [he]
  simp

end ContinuumCoulomb

end

end OAI
