import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumReferenceLower

namespace OAI

/-! Full-space variational comparison for the actual distributed reference family. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem qmaReferenceExtension_gram (n : ℕ) :
    (qmaReferenceExtension (α := α) n).conjTranspose*qmaReferenceExtension (α := α) n = 1 := by
  unfold qmaReferenceExtension
  rw [Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,←Matrix.mul_kronecker_mul,
    qmaReferenceTensor_gram,one_mul,Matrix.one_kronecker_one]

theorem qmaReferenceExtension_cogram (n : ℕ) :
    qmaReferenceExtension (α := α) n*(qmaReferenceExtension (α := α) n).conjTranspose = 1 :=
  mul_eq_one_comm.mp (qmaReferenceExtension_gram n)

theorem qmaReferenceExtension_mass (n : ℕ) (u : SourceSpinBasis n × α → ℂ) :
    (∑ p, Complex.normSq ((qmaReferenceExtension (α := α) n).mulVec u p)) =
      ∑ p, Complex.normSq (u p) := by
  rw [←qmaQuadratic_gram,qmaReferenceExtension_gram,qmaQuadratic_identity]

theorem qmaReferenceFamily_lower (n : ℕ) (A : Fin (n+1) → Matrix α α ℂ)
    (hpos : ∀ i u, 0 ≤ qmaQuadratic (A i) u) (a Δ : ℝ) (ha : 0 ≤ a) (hΔ : a ≤ Δ)
    (hA : ∀ u, a*(∑ i, Complex.normSq (u i)) ≤ qmaQuadratic (∑ i, A i) u)
    (u : SourceSpinBasis (n+1) × α → ℂ) :
    a*(∑ p, Complex.normSq (u p)) ≤ qmaQuadratic (qmaReferenceFamily n A Δ) u := by
  let B := qmaReferenceExtension (α := α) (n+1)
  let v := B.conjTranspose.mulVec u
  have hv : B.mulVec v = u := by
    change B.mulVec (B.conjTranspose.mulVec u) = u
    rw [Matrix.mulVec_mulVec,qmaReferenceExtension_cogram,Matrix.one_mulVec]
  have hm : (∑ p, Complex.normSq (v p)) = ∑ p, Complex.normSq (u p) := by
    rw [←hv,qmaReferenceExtension_mass]
  calc
    _ = ∑ s, a*(∑ i, Complex.normSq (v (s,i))) := by
      rw [←hm,Fintype.sum_prod_type,Finset.mul_sum]
    _ ≤ ∑ s, qmaQuadratic (qmaReferenceSector n A Δ s) (fun i => v (s,i)) :=
      Finset.sum_le_sum (fun s _ => qmaReferenceSector_lower n A hpos a Δ ha hΔ hA s _)
    _ = qmaQuadratic (qmaReferenceBlocks (n+1) (qmaReferenceSector n A Δ)) v :=
      (qmaReferenceBlocks_quadratic _ _ _).symm
    _ = qmaQuadratic (qmaReferenceFamily n A Δ) (B.mulVec v) := by
      rw [←qmaReferenceFamily_diagonalized,qmaQuadratic_change_basis]
    _ = _ := by rw [hv]

def qmaReferenceTrial (n : ℕ) (u : α → ℂ) : SourceSpinBasis (n+1) × α → ℂ :=
  (qmaReferenceExtension (α := α) (n+1)).mulVec
    (fun p => if p.1 = (fun _ => 1) then u p.2 else 0)

theorem qmaReferenceTrial_energy (n : ℕ) (A : Fin (n+1) → Matrix α α ℂ)
    (Δ : ℝ) (u : α → ℂ) :
    qmaQuadratic (qmaReferenceFamily n A Δ) (qmaReferenceTrial n u) =
      qmaQuadratic (∑ i, A i) u := by
  unfold qmaReferenceTrial
  rw [←qmaQuadratic_change_basis,qmaReferenceFamily_diagonalized,qmaReferenceBlocks_quadratic]
  rw [Finset.sum_eq_single (fun _ => (1:Fin 2))]
  · simp only [ite_true,qmaReferenceSector_one]
  · intro s _ hs
    simp only [hs,ite_false]
    simp [qmaQuadratic,Matrix.mulVec,dotProduct]
  · simp

theorem qmaReferenceTrial_mass (n : ℕ) (u : α → ℂ) :
    (∑ p, Complex.normSq (qmaReferenceTrial n u p)) = ∑ i, Complex.normSq (u i) := by
  unfold qmaReferenceTrial
  rw [qmaReferenceExtension_mass,Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (fun _ => (1:Fin 2))]
  · simp
  · intro s _ hs
    simp [hs]
  · simp

end ContinuumCoulomb

end

end OAI
