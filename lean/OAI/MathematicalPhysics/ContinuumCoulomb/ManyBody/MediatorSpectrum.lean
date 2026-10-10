import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorForms

namespace OAI

/-! Actual variational bottoms for the complete simultaneous-mediator spin
Hamiltonian and its effective source matrix. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

def mediatorFullBottom (n r : ℕ)
    (H : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ) : ℝ :=
  sInf {e | ∃ x : MediatorFullSpace n r, 0 < ‖x‖ ^ 2 ∧
    e = ⟪x, spinMatrixOperator H x⟫_ℝ / ‖x‖ ^ 2}

def sourceMatrixBottom (n : ℕ)
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) : ℝ :=
  sInf {e | ∃ p : MediatorLowSpace n, ‖p‖ = 1 ∧ e = ⟪p, spinMatrixOperator M p⟫_ℝ}

theorem mediatorFullBottom_eq_lowBlockBottom (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    mediatorFullBottom n r (bellMediatorHamiltonian n r Delta C left right member amplitude) =
      Perturbation.lowBlockBottom (actualMediatorLowBlock n r C)
        (diagonalPenalty (actualMediatorWeight n r Delta))
        (actualMediatorHighBlock n r C left right member amplitude)
        (actualMediatorCoupling n r left right member amplitude) := by
  unfold mediatorFullBottom Perturbation.lowBlockBottom
  congr 1
  ext e
  constructor
  · rintro ⟨x, hx, rfl⟩
    let p := mediatorLowRestriction n r x
    let q := mediatorHighRestriction n r x
    have hassemble : assembleMediator n r p q = x := mediator_full_decomposition n r x
    have hnorm : 0 < ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
      rw [← assembleMediator_norm_sq, hassemble]
      exact hx
    refine ⟨p, q, hnorm, ?_⟩
    unfold Perturbation.lowBlockRayleigh
    rw [← bellMediatorHamiltonian_form_blocks n r Delta C hC left right member amplitude,
      ← assembleMediator_norm_sq, hassemble]
  · rintro ⟨p, q, hpq, rfl⟩
    refine ⟨assembleMediator n r p q, ?_, ?_⟩
    · rw [assembleMediator_norm_sq]
      exact hpq
    · rw [bellMediatorHamiltonian_form_blocks n r Delta C hC left right member amplitude,
        assembleMediator_norm_sq]
      rfl

theorem actualMediator_effectiveBottom_matrix (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    Perturbation.effectiveBottom (actualMediatorLowBlock n r C)
      (diagonalPenalty (fun s => (actualMediatorWeight n r Delta s)⁻¹))
      (actualMediatorCoupling n r left right member amplitude) =
      sourceMatrixBottom n (C - mediatorCompression n r
        (totalMediatorSpokes n r left right member amplitude * liftedMediatorInverse n r Delta *
          totalMediatorSpokes n r left right member amplitude)) := by
  unfold Perturbation.effectiveBottom sourceMatrixBottom
  simp_rw [actualMediator_effectiveForm]

theorem sourceMatrixBottom_minimizer (n : ℕ)
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    ∃ p : MediatorLowSpace n, ‖p‖ = 1 ∧
      sourceMatrixBottom n M = ⟪p, spinMatrixOperator M p⟫_ℝ ∧
      ∀ q : MediatorLowSpace n, ‖q‖ = 1 →
        ⟪p, spinMatrixOperator M p⟫_ℝ ≤ ⟪q, spinMatrixOperator M q⟫_ℝ := by
  let C := (spinMatrixOperator M).restrictScalars ℝ
  let T : MediatorLowSpace n →L[ℝ] MediatorLowSpace n := 0
  let B : MediatorLowSpace n →L[ℝ] MediatorLowSpace n := 0
  let u : MediatorLowSpace n := EuclideanSpace.single (fun _ => 0) 1
  have hu : ‖u‖ = 1 := by simp [u]
  obtain ⟨p, hp, hmin⟩ := Perturbation.effectiveForm_minimizer C T B u hu
  have hform (q : MediatorLowSpace n) :
      Perturbation.effectiveForm C T B q = ⟪q, spinMatrixOperator M q⟫_ℝ := by
    simp [Perturbation.effectiveForm, Perturbation.inverseForm, C, T, B]
  have hbottom : Perturbation.effectiveBottom C T B = sourceMatrixBottom n M := by
    unfold Perturbation.effectiveBottom sourceMatrixBottom
    simp_rw [hform]
  refine ⟨p, hp, ?_, ?_⟩
  · rw [← hbottom, Perturbation.effectiveBottom_eq C T B p hp hmin, hform]
  · intro q hq
    simpa only [hform, hq, one_pow, mul_one] using hmin q

theorem sourceMatrixForm_shift (n : ℕ)
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (k : ℝ)
    (p : MediatorLowSpace n) (hp : ‖p‖ = 1) :
    ⟪p, spinMatrixOperator (M - (k : ℂ) • 1) p⟫_ℝ =
      ⟪p, spinMatrixOperator M p⟫_ℝ - k := by
  rw [spinMatrixOperator_sub, spinMatrixOperator_smul, spinMatrixOperator_one,
    _root_.sub_apply, _root_.smul_apply, one_apply_eq_self,
    inner_sub_right]
  have hscalar : ⟪p, (k : ℂ) • p⟫_ℝ = k := by
    rw [HubbardGlobal.euclidean_real_inner, inner_smul_right, inner_self_eq_norm_sq_to_K, hp]
    simp
  rw [hscalar]

theorem sourceMatrixBottom_shift (n : ℕ)
    (M : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (k : ℝ) :
    sourceMatrixBottom n (M - (k : ℂ) • 1) = sourceMatrixBottom n M - k := by
  obtain ⟨p, hp, hbottom, hmin⟩ := sourceMatrixBottom_minimizer n M
  let S := {e | ∃ q : MediatorLowSpace n, ‖q‖ = 1 ∧
    e = ⟪q, spinMatrixOperator (M - (k : ℂ) • 1) q⟫_ℝ}
  have hmem : ⟪p, spinMatrixOperator (M - (k : ℂ) • 1) p⟫_ℝ ∈ S := ⟨p, hp, rfl⟩
  have hlower : ∀ e ∈ S, sourceMatrixBottom n M - k ≤ e := by
    rintro e ⟨q, hq, rfl⟩
    rw [sourceMatrixForm_shift n M k q hq, hbottom]
    exact sub_le_sub_right (hmin q hq) k
  have hbdd : BddBelow S := ⟨_, hlower⟩
  apply le_antisymm
  · exact (csInf_le hbdd hmem).trans_eq (by rw [sourceMatrixForm_shift n M k p hp, hbottom])
  · exact le_csInf ⟨_, hmem⟩ hlower

/-- Full simultaneous singlet-mediator spectrum, retaining unreplaced
terms C and the exact constant shift. This compares actual variational
infima and has only explicit construction norm/calibration hypotheses. -/
theorem simultaneousMediator_bottom (n r : ℕ) {Delta : ℝ} (hDelta : 0 < Delta)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (left right : Fin r → Fin n) (hneq : ∀ e, left e ≠ right e)
    (J amplitude : Fin r → ℝ) (hcal : ∀ e, amplitude e ^ 2 = 2 * Delta * |J e|)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 4)
    (hbound : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      6 * ∑ e, |amplitude e| ≤ epsilon * (4 * Delta)) :
    |mediatorFullBottom n r (bellMediatorHamiltonian n r Delta C left right
        (fun e => signedMediatorMember (J e)) amplitude) + 3 * ∑ e, |J e| -
      sourceMatrixBottom n (C + ∑ e, (J e : ℂ) • sourceHeisenbergMatrix n (left e) (right e))| ≤
        16 * Delta * epsilon ^ 3 := by
  have h := actualMediator_second_order n r hDelta C left right
    (fun e => signedMediatorMember (J e)) amplitude hepsilon hsmall hbound
  rw [← mediatorFullBottom_eq_lowBlockBottom n r Delta C hC left right
    (fun e => signedMediatorMember (J e)) amplitude,
    actualMediator_effectiveBottom_matrix,
    signedMediator_effective_matrix n r hDelta left right hneq J amplitude hcal] at h
  have hshift : (C + ∑ e, (J e : ℂ) • sourceHeisenbergMatrix n (left e) (right e)) -
      (3 * ∑ e, |J e| : ℝ) • 1 =
      (C + ∑ e, (J e : ℂ) • sourceHeisenbergMatrix n (left e) (right e)) -
      ((3 * ∑ e, |J e| : ℝ) : ℂ) • 1 := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  rw [hshift, sourceMatrixBottom_shift] at h
  convert h using 1
  congr 1
  ring

end ContinuumCoulomb

end

end OAI
