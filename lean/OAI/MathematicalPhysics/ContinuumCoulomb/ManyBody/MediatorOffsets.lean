import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorPhysical

namespace OAI

/-! Exact scalar offsets relating the shifted mediator penalty to the
physical Hamiltonian containing only the specified Heisenberg bonds. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

theorem mediatorLocal_add (r : ℕ) (e : Fin r) (M N : Matrix (Fin 4) (Fin 4) ℂ) :
    mediatorLocal r e (M + N) = mediatorLocal r e M + mediatorLocal r e N := by
  ext a b
  simp only [mediatorLocal_apply, Matrix.add_apply, add_mul]

theorem mediatorLocal_smul (r : ℕ) (e : Fin r) (c : ℂ) (M : Matrix (Fin 4) (Fin 4) ℂ) :
    mediatorLocal r e (c • M) = c • mediatorLocal r e M := by
  ext a b
  simp only [mediatorLocal_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem physicalMediatorPenalty_offset (r : ℕ) (Delta : ℝ) :
    physicalMediatorPenalty r Delta =
      (Delta : ℂ) • (∑ e : Fin r, mediatorLocal r e heisenberg) +
        ((3 * r * Delta : ℝ) : ℂ) • 1 := by
  unfold physicalMediatorPenalty
  simp_rw [mediatorLocal_add, mediatorLocal_smul, mediatorLocal_one]
  rw [Finset.sum_add_distrib, smul_add]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  congr 1
  push_cast
  ring

def physicalRawMediatorHamiltonian (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  (1 : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) ⊗ₖ
      ((Delta : ℂ) • ∑ e, mediatorLocal r e heisenberg) +
    (C ⊗ₖ 1 + physicalTotalMediatorSpokes n r left right member amplitude)

theorem physicalMediatorHamiltonian_offset (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    physicalMediatorHamiltonian n r Delta C left right member amplitude =
      physicalRawMediatorHamiltonian n r Delta C left right member amplitude +
        ((3 * r * Delta : ℝ) : ℂ) • 1 := by
  unfold physicalMediatorHamiltonian physicalRawMediatorHamiltonian
  rw [physicalMediatorPenalty_offset, Matrix.kronecker_add, Matrix.kronecker_smul,
    Matrix.kronecker_smul, Matrix.one_kronecker_one]
  abel

theorem mediatorFullForm_add_scalar (n r : ℕ)
    (H : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ) (k : ℝ)
    (x : MediatorFullSpace n r) :
    ⟪x, spinMatrixOperator (H + (k : ℂ) • 1) x⟫_ℝ =
      ⟪x, spinMatrixOperator H x⟫_ℝ + k * ‖x‖ ^ 2 := by
  rw [spinMatrixOperator_add, spinMatrixOperator_smul, spinMatrixOperator_one,
    _root_.add_apply, _root_.smul_apply, one_apply_eq_self, inner_add_right]
  have hscalar : ⟪x, (k : ℂ) • x⟫_ℝ = k * ‖x‖ ^ 2 := by
    rw [HubbardGlobal.euclidean_real_inner, inner_smul_right, inner_self_eq_norm_sq_to_K]
    change ((k : ℂ) * (‖x‖ : ℂ) ^ 2).re = k * ‖x‖ ^ 2
    norm_cast
  rw [hscalar]

theorem mediatorFullBottom_add_scalar (n r : ℕ)
    (H : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ) (k : ℝ) :
    mediatorFullBottom n r (H + (k : ℂ) • 1) = mediatorFullBottom n r H + k := by
  let S := {e | ∃ x : MediatorFullSpace n r, 0 < ‖x‖ ^ 2 ∧
    e = ⟪x, spinMatrixOperator H x⟫_ℝ / ‖x‖ ^ 2}
  have hnonempty : S.Nonempty := by
    let x : MediatorFullSpace n r := EuclideanSpace.single ((fun _ => 0), mediatorVacuum r) 1
    refine ⟨_, x, ?_, rfl⟩
    simp [x]
  have hbounded : BddBelow S := by
    refine ⟨-‖spinMatrixOperator H‖, ?_⟩
    rintro e ⟨x, hx, rfl⟩
    have hform : |⟪x, spinMatrixOperator H x⟫_ℝ| ≤ ‖spinMatrixOperator H‖ * ‖x‖ ^ 2 := by
      calc
        _ ≤ ‖x‖ * ‖spinMatrixOperator H x‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖x‖ * (‖spinMatrixOperator H‖ * ‖x‖) :=
          mul_le_mul_of_nonneg_left ((spinMatrixOperator H).le_opNorm x) (norm_nonneg _)
        _ = _ := by ring
    exact (le_div_iff₀ hx).mpr (by nlinarith [(abs_le.mp hform).1])
  have hset : {e | ∃ x : MediatorFullSpace n r, 0 < ‖x‖ ^ 2 ∧
      e = ⟪x, spinMatrixOperator (H + (k : ℂ) • 1) x⟫_ℝ / ‖x‖ ^ 2} =
      (OrderIso.addRight k) '' S := by
    ext e
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟪x, spinMatrixOperator H x⟫_ℝ / ‖x‖ ^ 2, ⟨x, hx, rfl⟩, ?_⟩
      change _ + k = _
      rw [mediatorFullForm_add_scalar, add_div, mul_div_cancel_right₀ _ (ne_of_gt hx)]
    · rintro ⟨e, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      change _ + k = _
      rw [mediatorFullForm_add_scalar, add_div, mul_div_cancel_right₀ _ (ne_of_gt hx)]
  unfold mediatorFullBottom
  rw [hset]
  exact ((OrderIso.addRight k).map_csInf' hnonempty hbounded).symm

/-- Complete physical signed-to-positive mediator spectrum, with both
central-bond and spoke self-energy offsets displayed explicitly. -/
theorem physicalRawSimultaneousMediator_bottom (n r : ℕ) {Delta : ℝ} (hDelta : 0 < Delta)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (left right : Fin r → Fin n) (hneq : ∀ e, left e ≠ right e)
    (J amplitude : Fin r → ℝ) (hcal : ∀ e, amplitude e ^ 2 = 2 * Delta * |J e|)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 4)
    (hbound : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      6 * ∑ e, |amplitude e| ≤ epsilon * (4 * Delta)) :
    |mediatorFullBottom n r (physicalRawMediatorHamiltonian n r Delta C left right
        (fun e => signedMediatorMember (J e)) amplitude) + 3 * r * Delta + 3 * ∑ e, |J e| -
      sourceMatrixBottom n (C + ∑ e, (J e : ℂ) • sourceHeisenbergMatrix n (left e) (right e))| ≤
        16 * Delta * epsilon ^ 3 := by
  have h := physicalSimultaneousMediator_bottom n r hDelta C hC left right hneq J amplitude hcal
    hepsilon hsmall hbound
  rw [physicalMediatorHamiltonian_offset, mediatorFullBottom_add_scalar] at h
  exact h


/-- Canonical nonnegative spoke amplitudes, rather than arbitrary choices
satisfying only a square calibration. -/
theorem physicalCanonicalMediator_bottom (n r : ℕ) {Delta : ℝ} (hDelta : 0 < Delta)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (left right : Fin r → Fin n) (hneq : ∀ e, left e ≠ right e) (J : Fin r → ℝ)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 4)
    (hbound : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      6 * ∑ e, signedMediatorAmplitude Delta (J e) ≤ epsilon * (4 * Delta)) :
    |mediatorFullBottom n r (physicalRawMediatorHamiltonian n r Delta C left right
        (fun e => signedMediatorMember (J e)) (fun e => signedMediatorAmplitude Delta (J e))) +
        3 * r * Delta + 3 * ∑ e, |J e| -
      sourceMatrixBottom n (C + ∑ e, (J e : ℂ) • sourceHeisenbergMatrix n (left e) (right e))| ≤
        16 * Delta * epsilon ^ 3 := by
  apply physicalRawSimultaneousMediator_bottom n r hDelta C hC left right hneq J _
    (fun e => signedMediatorAmplitude_calibration hDelta.le (J e)) hepsilon hsmall
  simpa only [abs_of_nonneg (signedMediatorAmplitude_nonneg _ _)] using hbound

end ContinuumCoulomb

end

end OAI
