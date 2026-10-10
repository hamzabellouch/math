import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingBlocks

namespace OAI

/-! Exact quadratic forms for the finite singlet routing gadgets. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

theorem routingLowRestriction_low (n r : ℕ)
    (W : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ)
    (hWlow : mediatorCompression n r W = 0) (p : MediatorLowSpace n) :
    mediatorLowRestriction n r (spinMatrixOperator W
      (mediatorLowInclusion n r p)) = 0 := by
  have h := congrArg (fun T : MediatorLowSpace n →L[ℂ] MediatorLowSpace n => T p)
    (mediatorLow_operator_compression n r W)
  simpa only [ContinuousLinearMap.comp_apply, hWlow,
    spinMatrixOperator_zero, _root_.zero_apply] using h

/-- Hopping a singlet-sector state creates only actual mediator excitations. -/
theorem routingHighInclusion_coupling (n r : ℕ)
    (W : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ)
    (hWlow : mediatorCompression n r W = 0) (p : MediatorLowSpace n) :
    mediatorHighInclusion n r (routingCoupling n r W p) =
      spinMatrixOperator W
        (mediatorLowInclusion n r p) := by
  change mediatorHighInclusion n r (mediatorHighRestriction n r
    (spinMatrixOperator W
      (mediatorLowInclusion n r p))) = _
  have h := mediator_full_decomposition n r
    (spinMatrixOperator W
      (mediatorLowInclusion n r p))
  simpa only [routingLowRestriction_low n r W hWlow, map_zero, zero_add] using h

/-- The actual full matrix in the complete Bell-coordinate spin space. -/
def routingHamiltonian (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (W : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  bellMediatorPenaltyMatrix n r Delta +
    (C ⊗ₖ 1 + W)

/-- Exact effective quadratic form for every entangled original-spin vector. -/
theorem routing_effectiveForm (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (W : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ)
    (hW : W.conjTranspose = W) (hWlow : mediatorCompression n r W = 0)
    (p : MediatorLowSpace n) :
    Perturbation.effectiveForm (actualMediatorLowBlock n r C)
      (diagonalPenalty (fun s => (actualMediatorWeight n r Delta s)⁻¹))
      (routingCoupling n r W) p =
      ⟪p, spinMatrixOperator (C - mediatorCompression n r
        (W * liftedMediatorInverse n r Delta *
          W)) p⟫_ℝ := by
  let B := routingCoupling n r W
  let T := diagonalPenalty (fun s => (actualMediatorWeight n r Delta s)⁻¹)
  have hB : mediatorHighInclusion n r (B p) = spinMatrixOperator W (mediatorLowInclusion n r p) :=
    routingHighInclusion_coupling n r W hWlow p
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
        (spinMatrixOperator_real_symmetric W hW _ _).symm
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


/-- Full-state quadratic-form equality for the concrete low/high blocks. -/
theorem routingHamiltonian_form_blocks (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (W : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ)
    (hW : W.conjTranspose = W) (hWlow : mediatorCompression n r W = 0)
    (p : MediatorLowSpace n) (q : MediatorHighSpace n r) :
    ⟪assembleMediator n r p q,
      spinMatrixOperator (routingHamiltonian n r Delta C W)
        (assembleMediator n r p q)⟫_ℝ =
      Perturbation.lowBlockEnergy (actualMediatorLowBlock n r C)
        (diagonalPenalty (actualMediatorWeight n r Delta))
        (routingHighBlock n r C W)
        (routingCoupling n r W) p q := by
  let H := spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ) + W)
  let P := spinMatrixOperator (bellMediatorPenaltyMatrix n r Delta)
  let lp := mediatorLowInclusion n r p
  let hq := mediatorHighInclusion n r q
  have hHermitian : (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ) + W).conjTranspose =
      C ⊗ₖ 1 + W := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker, hC,
      Matrix.conjTranspose_one, hW]
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
      mediatorLow_real_inner, routingLowRestriction_low n r W hWlow, inner_zero_right, add_zero,
      actualMediatorLowBlock_eq]
    rfl
  have hCross : ⟪hq, H lp⟫_ℝ =
      ⟪q, routingCoupling n r W p⟫_ℝ := by
    rw [hHlow, inner_add_right, mediatorHigh_real_inner, mediatorHighRestriction_low,
      inner_zero_right, zero_add, mediatorHigh_real_inner]
    rfl
  have hReverse : ⟪lp, H hq⟫_ℝ =
      ⟪q, routingCoupling n r W p⟫_ℝ := by
    rw [spinMatrixOperator_real_symmetric _ hHermitian, real_inner_comm, hCross]
  have hHigh : ⟪hq, H hq⟫_ℝ =
      ⟪q, routingHighBlock n r C W q⟫_ℝ := by
    rw [mediatorHigh_real_inner]
    rfl
  have hform : ⟪assembleMediator n r p q,
      spinMatrixOperator (routingHamiltonian n r Delta C W)
        (assembleMediator n r p q)⟫_ℝ =
      ⟪lp + hq, P (lp + hq) + H (lp + hq)⟫_ℝ := by
    unfold routingHamiltonian assembleMediator
    rw [spinMatrixOperator_add, _root_.add_apply]
  rw [hform, map_add, map_add]
  simp only [inner_add_left, inner_add_right, hPlow, inner_zero_right,
    hPenaltyCross, hPenaltyHigh, hLow, hCross, hReverse, hHigh,
    Perturbation.lowBlockEnergy, Perturbation.blockEnergy, Perturbation.penaltyForm]
  ring

end ContinuumCoulomb

end

end OAI
