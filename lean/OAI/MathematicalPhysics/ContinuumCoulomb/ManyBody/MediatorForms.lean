import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorSector

namespace OAI

/-! Full simultaneous-mediator quadratic forms and their exact effective matrix. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

@[simp] theorem spinMatrixOperator_zero {ι : Type*} [Fintype ι] [DecidableEq ι] :
    spinMatrixOperator (0 : Matrix ι ι ℂ) = 0 := by
  unfold spinMatrixOperator
  rw [map_zero, map_zero]

@[simp] theorem spinMatrixOperator_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : Matrix ι ι ℂ) : spinMatrixOperator (M - N) = spinMatrixOperator M - spinMatrixOperator N := by
  unfold spinMatrixOperator
  rw [map_sub, map_sub]

theorem spinMatrixOperator_real_symmetric {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (hM : M.conjTranspose = M) (x y : EuclideanSpace ℂ ι) :
    ⟪x, spinMatrixOperator M y⟫_ℝ = ⟪spinMatrixOperator M x, y⟫_ℝ := by
  rw [HubbardGlobal.euclidean_real_inner, HubbardGlobal.euclidean_real_inner]
  have h := ContinuousLinearMap.adjoint_inner_right (spinMatrixOperator M) x y
  rw [← spinMatrixOperator_star, hM] at h
  exact congrArg Complex.re h

theorem actualMediatorLowBlock_eq (n r : ℕ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    actualMediatorLowBlock n r C = (spinMatrixOperator C).restrictScalars ℝ := by
  unfold actualMediatorLowBlock
  rw [mediatorLow_operator_compression, mediatorCompression_kronecker]
  simp

theorem mediatorLowRestriction_spokes_low (n r : ℕ) (left right : Fin r → Fin n)
    (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) (p : MediatorLowSpace n) :
    mediatorLowRestriction n r (spinMatrixOperator (totalMediatorSpokes n r left right member amplitude)
      (mediatorLowInclusion n r p)) = 0 := by
  have h := congrArg (fun T : MediatorLowSpace n →L[ℂ] MediatorLowSpace n => T p)
    (mediatorLow_operator_compression n r (totalMediatorSpokes n r left right member amplitude))
  simpa only [ContinuousLinearMap.comp_apply, totalMediatorSpokes_low_compression,
    spinMatrixOperator_zero, _root_.zero_apply] using h

/-- Hopping a singlet-sector state creates only actual mediator excitations. -/
theorem mediatorHighInclusion_coupling (n r : ℕ) (left right : Fin r → Fin n)
    (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) (p : MediatorLowSpace n) :
    mediatorHighInclusion n r (actualMediatorCoupling n r left right member amplitude p) =
      spinMatrixOperator (totalMediatorSpokes n r left right member amplitude)
        (mediatorLowInclusion n r p) := by
  change mediatorHighInclusion n r (mediatorHighRestriction n r
    (spinMatrixOperator (totalMediatorSpokes n r left right member amplitude)
      (mediatorLowInclusion n r p))) = _
  have h := mediator_full_decomposition n r
    (spinMatrixOperator (totalMediatorSpokes n r left right member amplitude)
      (mediatorLowInclusion n r p))
  simpa only [mediatorLowRestriction_spokes_low, map_zero, zero_add] using h

def bellMediatorPenaltyMatrix (n r : ℕ) (Delta : ℝ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  Matrix.diagonal (fun s => (mediatorPenaltyWeight r Delta s.2 : ℂ))

theorem bellMediatorPenalty_low (n r : ℕ) (Delta : ℝ) (p : MediatorLowSpace n) :
    spinMatrixOperator (bellMediatorPenaltyMatrix n r Delta) (mediatorLowInclusion n r p) = 0 := by
  classical
  ext ⟨s, a⟩
  rw [bellMediatorPenaltyMatrix, spinMatrixOperator_diagonal, mediatorLowInclusion_apply]
  by_cases ha : a = mediatorVacuum r
  · subst a
    simp [mediatorPenaltyWeight, mediatorExcitationNumber, mediatorVacuum]
  · simp [ha]

theorem bellMediatorPenalty_high (n r : ℕ) (Delta : ℝ) (q : MediatorHighSpace n r) :
    spinMatrixOperator (bellMediatorPenaltyMatrix n r Delta) (mediatorHighInclusion n r q) =
      mediatorHighInclusion n r (diagonalPenalty (actualMediatorWeight n r Delta) q) := by
  classical
  ext ⟨s, a⟩
  rw [bellMediatorPenaltyMatrix, spinMatrixOperator_diagonal]
  by_cases ha : a = mediatorVacuum r
  · subst a
    simp only [mediatorHighInclusion_vacuum, mul_zero]
  · rw [mediatorHighInclusion_apply n r q s ⟨a, ha⟩,
      mediatorHighInclusion_apply n r _ s ⟨a, ha⟩]
    simp only [diagonalPenalty_apply, actualMediatorWeight, RCLike.real_smul_eq_coe_mul]
    rfl

/-- The actual full matrix in the complete Bell-coordinate spin space. -/
def bellMediatorHamiltonian (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  bellMediatorPenaltyMatrix n r Delta +
    (C ⊗ₖ 1 + totalMediatorSpokes n r left right member amplitude)

/-- Exact effective quadratic form for every entangled original-spin vector. -/
theorem actualMediator_effectiveForm (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ)
    (p : MediatorLowSpace n) :
    Perturbation.effectiveForm (actualMediatorLowBlock n r C)
      (diagonalPenalty (fun s => (actualMediatorWeight n r Delta s)⁻¹))
      (actualMediatorCoupling n r left right member amplitude) p =
      ⟪p, spinMatrixOperator (C - mediatorCompression n r
        (totalMediatorSpokes n r left right member amplitude * liftedMediatorInverse n r Delta *
          totalMediatorSpokes n r left right member amplitude)) p⟫_ℝ := by
  let W := totalMediatorSpokes n r left right member amplitude
  let B := actualMediatorCoupling n r left right member amplitude
  let T := diagonalPenalty (fun s => (actualMediatorWeight n r Delta s)⁻¹)
  have hB : mediatorHighInclusion n r (B p) = spinMatrixOperator W (mediatorLowInclusion n r p) :=
    mediatorHighInclusion_coupling n r left right member amplitude p
  have hT : mediatorHighInclusion n r (T (B p)) =
      spinMatrixOperator (liftedMediatorInverse n r Delta) (mediatorHighInclusion n r (B p)) :=
    (mediatorInverse_highInclusion n r Delta (B p)).symm
  have hinner : ⟪B p, T (B p)⟫_ℝ =
      ⟪p, spinMatrixOperator (mediatorCompression n r
        (W * liftedMediatorInverse n r Delta * W)) p⟫_ℝ := by
    calc
      _ = ⟪mediatorHighInclusion n r (B p), mediatorHighInclusion n r (T (B p))⟫_ℝ := by
        rw [mediatorHigh_real_inner, mediatorHighRestriction_inclusion]
      _ = ⟪spinMatrixOperator W (mediatorLowInclusion n r p),
          spinMatrixOperator (liftedMediatorInverse n r Delta)
            (spinMatrixOperator W (mediatorLowInclusion n r p))⟫_ℝ := by rw [hT, hB]
      _ = ⟪mediatorLowInclusion n r p, spinMatrixOperator W
          (spinMatrixOperator (liftedMediatorInverse n r Delta)
            (spinMatrixOperator W (mediatorLowInclusion n r p)))⟫_ℝ :=
        (spinMatrixOperator_real_symmetric W (totalMediatorSpokes_star n r left right member amplitude) _ _).symm
      _ = ⟪p, spinMatrixOperator (mediatorCompression n r
          (W * liftedMediatorInverse n r Delta * W)) p⟫_ℝ := by
        rw [mediatorLow_real_inner]
        have hc := congrArg (fun A : MediatorLowSpace n →L[ℂ] MediatorLowSpace n => A p)
          (mediatorLow_operator_compression n r (W * liftedMediatorInverse n r Delta * W))
        simpa only [spinMatrixOperator_mul, ContinuousLinearMap.comp_apply] using congrArg
          (fun x : MediatorLowSpace n => ⟪p, x⟫_ℝ) hc
  unfold Perturbation.effectiveForm Perturbation.inverseForm
  rw [actualMediatorLowBlock_eq, hinner, spinMatrixOperator_sub]
  simp only [ContinuousLinearMap.coe_restrictScalars', _root_.sub_apply, inner_sub_right]
  rfl


/-- Full-state quadratic-form equality for the concrete low/high blocks. -/
theorem bellMediatorHamiltonian_form_blocks (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ)
    (p : MediatorLowSpace n) (q : MediatorHighSpace n r) :
    ⟪assembleMediator n r p q,
      spinMatrixOperator (bellMediatorHamiltonian n r Delta C left right member amplitude)
        (assembleMediator n r p q)⟫_ℝ =
      Perturbation.lowBlockEnergy (actualMediatorLowBlock n r C)
        (diagonalPenalty (actualMediatorWeight n r Delta))
        (actualMediatorHighBlock n r C left right member amplitude)
        (actualMediatorCoupling n r left right member amplitude) p q := by
  let W := totalMediatorSpokes n r left right member amplitude
  let H := spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ) + W)
  let P := spinMatrixOperator (bellMediatorPenaltyMatrix n r Delta)
  let lp := mediatorLowInclusion n r p
  let hq := mediatorHighInclusion n r q
  have hHermitian : (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ) + W).conjTranspose =
      C ⊗ₖ 1 + W := by
    dsimp only [W]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker, hC,
      Matrix.conjTranspose_one, totalMediatorSpokes_star]
  have hPlow : P lp = 0 := bellMediatorPenalty_low n r Delta p
  have hPhigh : P hq = mediatorHighInclusion n r
      (diagonalPenalty (actualMediatorWeight n r Delta) q) := bellMediatorPenalty_high n r Delta q
  have hPenaltyCross : ⟪lp, P hq⟫_ℝ = 0 := by
    rw [hPhigh, mediatorLow_real_inner, mediatorLowRestriction_high, inner_zero_right]
  have hPenaltyHigh : ⟪hq, P hq⟫_ℝ =
      ⟪q, diagonalPenalty (actualMediatorWeight n r Delta) q⟫_ℝ := by
    rw [hPhigh, mediatorHigh_real_inner, mediatorHighRestriction_inclusion]
  have hHlow : H lp = mediatorLowInclusion n r (spinMatrixOperator C p) + spinMatrixOperator W lp := by
    dsimp only [H, lp]
    rw [spinMatrixOperator_add, _root_.add_apply, liftedSource_lowInclusion]
  have hLow : ⟪lp, H lp⟫_ℝ = ⟪p, actualMediatorLowBlock n r C p⟫_ℝ := by
    rw [hHlow, inner_add_right, mediatorLow_real_inner, mediatorLowRestriction_inclusion,
      mediatorLow_real_inner, mediatorLowRestriction_spokes_low, inner_zero_right, add_zero,
      actualMediatorLowBlock_eq]
    rfl
  have hCross : ⟪hq, H lp⟫_ℝ =
      ⟪q, actualMediatorCoupling n r left right member amplitude p⟫_ℝ := by
    rw [hHlow, inner_add_right, mediatorHigh_real_inner, mediatorHighRestriction_low,
      inner_zero_right, zero_add, mediatorHigh_real_inner]
    rfl
  have hReverse : ⟪lp, H hq⟫_ℝ =
      ⟪q, actualMediatorCoupling n r left right member amplitude p⟫_ℝ := by
    rw [spinMatrixOperator_real_symmetric _ hHermitian, real_inner_comm, hCross]
  have hHigh : ⟪hq, H hq⟫_ℝ =
      ⟪q, actualMediatorHighBlock n r C left right member amplitude q⟫_ℝ := by
    rw [mediatorHigh_real_inner]
    rfl
  have hform : ⟪assembleMediator n r p q,
      spinMatrixOperator (bellMediatorHamiltonian n r Delta C left right member amplitude)
        (assembleMediator n r p q)⟫_ℝ =
      ⟪lp + hq, P (lp + hq) + H (lp + hq)⟫_ℝ := by
    unfold bellMediatorHamiltonian assembleMediator
    rw [spinMatrixOperator_add, _root_.add_apply]
  rw [hform, map_add, map_add]
  simp only [inner_add_left, inner_add_right, hPlow, inner_zero_right,
    hPenaltyCross, hPenaltyHigh, hLow, hCross, hReverse, hHigh,
    Perturbation.lowBlockEnergy, Perturbation.blockEnergy, Perturbation.penaltyForm]
  ring

end ContinuumCoulomb

end

end OAI
