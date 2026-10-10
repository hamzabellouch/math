import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorSpectrum

namespace OAI

/-! Physical positive-spoke spin matrices and their full spectral comparison. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

def physicalMediatorEdgeSpoke (n r : ℕ) (e : Fin r) (i j : Fin n) (member : Fin 2) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  ∑ μ : Fin 3,
    (sourceLocalPauli n i μ ⊗ₖ mediatorLocal r e (physicalMemberPauli 0 μ) +
      sourceLocalPauli n j μ ⊗ₖ mediatorLocal r e (physicalMemberPauli member μ))

def physicalTotalMediatorSpokes (n r : ℕ) (left right : Fin r → Fin n)
    (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  ∑ e, (amplitude e : ℂ) • physicalMediatorEdgeSpoke n r e (left e) (right e) (member e)

/-- Central antiferromagnetic bonds with their explicit three-Delta
singlet shifts, plus the physical original-spin and spoke interactions. -/
def physicalMediatorHamiltonian (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  1 ⊗ₖ physicalMediatorPenalty r Delta +
    (C ⊗ₖ 1 + physicalTotalMediatorSpokes n r left right member amplitude)

theorem physicalMediatorPenalty_full_transform (n r : ℕ) (Delta : ℝ) :
    (fullMediatorBellMatrix n r).conjTranspose *
      ((1 : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) ⊗ₖ physicalMediatorPenalty r Delta) *
        fullMediatorBellMatrix n r = bellMediatorPenaltyMatrix n r Delta := by
  unfold fullMediatorBellMatrix
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]
  simp only [Matrix.conjTranspose_one, one_mul, physicalMediatorPenalty_diagonal]
  rw [← Matrix.diagonal_one (n := SourceSpinBasis n), Matrix.diagonal_kronecker_diagonal]
  simp only [one_mul]
  rfl

theorem liftedSource_full_transform (n r : ℕ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    (fullMediatorBellMatrix n r).conjTranspose *
      (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ)) * fullMediatorBellMatrix n r =
      C ⊗ₖ 1 := by
  unfold fullMediatorBellMatrix
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul]
  simp only [Matrix.conjTranspose_one, one_mul, mul_one, globalBellMatrix_gram]

theorem physicalMediatorEdgeSpoke_transform (n r : ℕ) (e : Fin r) (i j : Fin n) (member : Fin 2) :
    (fullMediatorBellMatrix n r).conjTranspose * physicalMediatorEdgeSpoke n r e i j member *
      fullMediatorBellMatrix n r = mediatorEdgeSpoke n r e i j member := by
  unfold physicalMediatorEdgeSpoke mediatorEdgeSpoke
  simp only [Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, physicalSpoke_bellTransform]

theorem physicalTotalMediatorSpokes_transform (n r : ℕ) (left right : Fin r → Fin n)
    (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    (fullMediatorBellMatrix n r).conjTranspose *
      physicalTotalMediatorSpokes n r left right member amplitude * fullMediatorBellMatrix n r =
        totalMediatorSpokes n r left right member amplitude := by
  unfold physicalTotalMediatorSpokes totalMediatorSpokes
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    physicalMediatorEdgeSpoke_transform]

/-- Exact change of coordinates for the entire physical construction. -/
theorem physicalMediatorHamiltonian_transform (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    (fullMediatorBellMatrix n r).conjTranspose *
      physicalMediatorHamiltonian n r Delta C left right member amplitude *
        fullMediatorBellMatrix n r = bellMediatorHamiltonian n r Delta C left right member amplitude := by
  unfold physicalMediatorHamiltonian bellMediatorHamiltonian
  simp only [mul_add, add_mul, physicalMediatorPenalty_full_transform,
    liftedSource_full_transform, physicalTotalMediatorSpokes_transform]

theorem spinMatrixOperator_unitary_form (n r : ℕ)
    (U H : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ)
    (x : MediatorFullSpace n r) :
    ⟪x, spinMatrixOperator (U.conjTranspose * H * U) x⟫_ℝ =
      ⟪spinMatrixOperator U x, spinMatrixOperator H (spinMatrixOperator U x)⟫_ℝ := by
  simp only [spinMatrixOperator_mul, spinMatrixOperator_star, ContinuousLinearMap.comp_apply]
  rw [HubbardGlobal.euclidean_real_inner, HubbardGlobal.euclidean_real_inner]
  exact congrArg Complex.re (ContinuousLinearMap.adjoint_inner_right
    (spinMatrixOperator U) x (spinMatrixOperator H (spinMatrixOperator U x)))

/-- The complete variational infimum is invariant under the explicit unitary. -/
theorem mediatorFullBottom_unitary (n r : ℕ)
    (U H : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ)
    (hGram : U.conjTranspose * U = 1) (hCogram : U * U.conjTranspose = 1) :
    mediatorFullBottom n r (U.conjTranspose * H * U) = mediatorFullBottom n r H := by
  unfold mediatorFullBottom
  congr 1
  ext e
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨spinMatrixOperator U x, ?_, ?_⟩
    · rw [spinMatrixOperator_unitary_norm_map U hGram]
      exact hx
    · rw [spinMatrixOperator_unitary_form, spinMatrixOperator_unitary_norm_map U hGram]
  · rintro ⟨x, hx, rfl⟩
    have hUstar : U.conjTranspose.conjTranspose * U.conjTranspose = 1 := by
      simpa only [Matrix.conjTranspose_conjTranspose] using hCogram
    have hcancel : spinMatrixOperator U (spinMatrixOperator U.conjTranspose x) = x := by
      have h := congrArg (fun M => spinMatrixOperator M x) hCogram
      simpa only [spinMatrixOperator_mul, ContinuousLinearMap.comp_apply,
        spinMatrixOperator_one, one_apply_eq_self] using h
    refine ⟨spinMatrixOperator U.conjTranspose x, ?_, ?_⟩
    · rw [spinMatrixOperator_unitary_norm_map U.conjTranspose hUstar]
      exact hx
    · rw [spinMatrixOperator_unitary_form, hcancel,
        spinMatrixOperator_unitary_norm_map U.conjTranspose hUstar]

/-- Physical full-spin spectral comparison for the simultaneous positive
singlet spokes, including all excited sectors and unreplaced terms. -/
theorem physicalSimultaneousMediator_bottom (n r : ℕ) {Delta : ℝ} (hDelta : 0 < Delta)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (left right : Fin r → Fin n) (hneq : ∀ e, left e ≠ right e)
    (J amplitude : Fin r → ℝ) (hcal : ∀ e, amplitude e ^ 2 = 2 * Delta * |J e|)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 4)
    (hbound : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      6 * ∑ e, |amplitude e| ≤ epsilon * (4 * Delta)) :
    |mediatorFullBottom n r (physicalMediatorHamiltonian n r Delta C left right
        (fun e => signedMediatorMember (J e)) amplitude) + 3 * ∑ e, |J e| -
      sourceMatrixBottom n (C + ∑ e, (J e : ℂ) • sourceHeisenbergMatrix n (left e) (right e))| ≤
        16 * Delta * epsilon ^ 3 := by
  have hbottom := mediatorFullBottom_unitary n r (fullMediatorBellMatrix n r)
    (physicalMediatorHamiltonian n r Delta C left right (fun e => signedMediatorMember (J e)) amplitude)
    (fullMediatorBellMatrix_gram n r) (fullMediatorBellMatrix_cogram n r)
  rw [physicalMediatorHamiltonian_transform] at hbottom
  rw [← hbottom]
  exact simultaneousMediator_bottom n r hDelta C hC left right hneq J amplitude hcal
    hepsilon hsmall hbound

end ContinuumCoulomb

end

end OAI
