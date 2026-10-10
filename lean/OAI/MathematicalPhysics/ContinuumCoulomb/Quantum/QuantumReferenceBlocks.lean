import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumDistributedRebit

namespace OAI

/-! Exact sector decomposition for distributed realification. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {α : Type*} [Fintype α] [DecidableEq α]

def qmaReferenceBlocks (n : ℕ) (B : SourceSpinBasis n → Matrix α α ℂ) :
    Matrix (SourceSpinBasis n × α) (SourceSpinBasis n × α) ℂ :=
  fun p q => if p.1 = q.1 then B p.1 p.2 q.2 else 0

omit [DecidableEq α] in
theorem qmaReferenceBlocks_quadratic (n : ℕ) (B : SourceSpinBasis n → Matrix α α ℂ)
    (u : SourceSpinBasis n × α → ℂ) :
    qmaQuadratic (qmaReferenceBlocks n B) u =
      ∑ s, qmaQuadratic (B s) (fun a => u (s,a)) := by
  simp [qmaQuadratic,qmaReferenceBlocks,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,
    Complex.re_sum]

omit [Fintype α] [DecidableEq α] in
theorem qmaReferenceBlocks_sum {κ : Type*} [Fintype κ] (n : ℕ)
    (B : κ → SourceSpinBasis n → Matrix α α ℂ) :
    qmaReferenceBlocks n (fun s => ∑ j, B j s) = ∑ j, qmaReferenceBlocks n (B j) := by
  ext ⟨s,a⟩ ⟨t,b⟩
  by_cases h : s = t <;> simp [qmaReferenceBlocks,Matrix.sum_apply,h]

omit [Fintype α] [DecidableEq α] in
theorem qmaReferenceBlocks_add (n : ℕ) (B C : SourceSpinBasis n → Matrix α α ℂ) :
    qmaReferenceBlocks n (fun s => B s+C s) = qmaReferenceBlocks n B+qmaReferenceBlocks n C := by
  ext ⟨s,a⟩ ⟨t,b⟩
  by_cases h : s = t <;> simp [qmaReferenceBlocks,h]

def qmaConjugateMatrix (A : Matrix α α ℂ) : Matrix α α ℂ :=
  fun a b => star (A a b)

def qmaReferenceSectorTerm (n : ℕ) (i : Fin n) (A : Matrix α α ℂ)
    (s : SourceSpinBasis n) : Matrix α α ℂ :=
  if s i = 0 then qmaConjugateMatrix A else A

theorem qmaDistributedRebitTerm_blocks (n : ℕ) (i : Fin n) (A : Matrix α α ℂ) :
    (qmaReferenceExtension (α := α) n).conjTranspose*qmaDistributedRebitTerm n i A*
      qmaReferenceExtension (α := α) n =
        qmaReferenceBlocks n (qmaReferenceSectorTerm n i A) := by
  ext ⟨s,a⟩ ⟨t,b⟩
  rw [qmaDistributedRebitTerm_block]
  by_cases hs : s = t
  · subst t
    by_cases hz : s i = 0 <;> simp [qmaReferenceBlocks,qmaReferenceSectorTerm,qmaConjugateMatrix,hz]
  · simp [qmaReferenceBlocks,hs]

theorem qmaReferencePenalty_blocks (n : ℕ) :
    (qmaReferenceExtension (α := α) (n+1)).conjTranspose*
      (qmaReferenceYPenalty n ⊗ₖ (1 : Matrix α α ℂ))*
        qmaReferenceExtension (α := α) (n+1) =
    qmaReferenceBlocks (n+1) (fun s => (qmaReferenceWalls n s : ℂ) • (1 : Matrix α α ℂ)) := by
  unfold qmaReferenceExtension
  rw [Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one]
  simp only [←Matrix.mul_kronecker_mul,one_mul,qmaReferenceYPenalty_diagonalized]
  ext ⟨s,a⟩ ⟨t,b⟩
  by_cases hs : s = t
  · subst t
    simp [qmaReferenceWallMatrix,qmaReferenceBlocks]
  · simp [qmaReferenceWallMatrix,qmaReferenceBlocks,hs]

end ContinuumCoulomb

end

end OAI
