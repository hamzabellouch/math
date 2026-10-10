import Mathlib
import OAI.Analysis.Commutator.AmplifiedProjectionBlocks
import OAI.Analysis.Commutator.CentralAtoms
import OAI.Analysis.Commutator.CentralAverage
import OAI.Analysis.Commutator.CentralBlockEstimate

namespace OAI

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.CentralAtoms

open ProjectionBlocks

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

omit [TopologicalSpace.SeparableSpace H] in
lemma block_commutes (M : VonNeumannAlgebra H) (Y : H →L[ℂ] H)
    (hy : ∀ p : Atom M,Y*projection M p=projection M p*Y)
    (h : ℕ) (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈M)
    (p : Atom M) :
    (diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y)*
      diagonalAmplification h (projection M p)=
    diagonalAmplification h (projection M p)*
      (diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y) := by
  let A := diagonalAmplification h Y
  let B := matrixOperator h X
  let Q := diagonalAmplification h (projection M p)
  have ha : A*Q=Q*A := by
    change OperatorAmplification.diagonal (H:=H) (Fin h) Y*
      OperatorAmplification.diagonal (H:=H) (Fin h) (projection M p)=_
    rw [←map_mul,hy p,map_mul]
    rfl
  have hb : B*Q=Q*B := (diagonal_matrix_commute h (projection M p) X
    (fun i j => (((CentralCorner.mem_center M _).mp p.property.1).2 (X i j) (hX i j)).symm)).symm
  change (A*B-B*A)*Q=Q*(A*B-B*A)
  calc
    _=A*(B*Q)-B*(A*Q) := by simp only [sub_mul,mul_assoc]
    _=A*(Q*B)-B*(Q*A) := by rw [ha,hb]
    _=(A*Q)*B-(B*Q)*A := by simp only [mul_assoc]
    _=(Q*A)*B-(Q*B)*A := by rw [ha,hb]
    _=_ := by simp only [mul_sub,mul_assoc]

theorem centered_bound (M : VonNeumannAlgebra H) (hat : IsAtomicCenter M)
    (Y : H →L[ℂ] H) (hy : ∀ p : Atom M,Y*projection M p=projection M p*Y)
    (h : ℕ) (hh : 1≤h) (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈M) :
    ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖≤
      3122*commutatorSeminorm M Y*‖matrixOperator h X‖ := by
  apply norm_le_of_blocks (fun p : Atom M => diagonalAmplification h (projection M p))
    (diagonal_projection (projection M) (isProjection M) h)
    (diagonal_orthogonal (projection M) (orthogonal M) h) _
    (mul_nonneg (mul_nonneg (by norm_num) (commutatorSeminorm_nonneg M Y)) (norm_nonneg _))
    (block_commutes M Y hy h X hX)
  · intro p ξ
    let pM : M := ⟨projection M p,((CentralCorner.mem_center M _).mp p.property.1).1⟩
    have hp : IsStarProjection pM :=
      ⟨Subtype.ext p.property.2.1.isIdempotentElem.eq,Subtype.ext p.property.2.1.isSelfAdjoint.star_eq⟩
    have hz : (pM:H →L[ℂ] H)∈Set.centralizer (M : Set (H →L[ℂ] H)) :=
      ((CentralCorner.mem_center M _).mp p.property.1).2
    exact CentralCorner.projected_vector_bound M hp hz p.property Y (hy p) h hh
      (fun i j => ⟨X i j,hX i j⟩) ξ
  · exact diagonal_full (projection M) (isProjection M) (orthogonal M) h (part_eq_one_of_atomic M hat)

theorem uniform_commutator_atomic_center (M : VonNeumannAlgebra H) (hat : IsAtomicCenter M)
    (Y : H →L[ℂ] H) (h : ℕ) (hh : 1≤h)
    (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈M) :
    ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖≤
      9368*commutatorSeminorm M Y*‖matrixOperator h X‖ := by
  obtain ⟨Z,hz,hd,_⟩ := CentralAverage.exists_center_average M Y
  have hc (p : Atom M) : Z*projection M p=projection M p*Z :=
    hz _ ((CentralCorner.mem_center M _).mp p.property.1).1
      ((CentralCorner.mem_center M _).mp p.property.1).2
  have hb := centered_bound M hat Z hc h hh X hX
  convert matrix_commutator_perturb M Y Z hd 3122 (by norm_num) h X hb using 1
  norm_num

end Kadison.CentralAtoms
end
end

end OAI
