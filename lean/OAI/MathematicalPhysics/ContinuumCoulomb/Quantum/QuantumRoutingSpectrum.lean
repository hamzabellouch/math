import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingForms
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorSpectrum

namespace OAI

/-! Ground-energy comparison on the complete spin space for routing gadgets. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

theorem routingFullBottom_eq_lowBlockBottom (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (W : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ)
    (hW : W.conjTranspose = W) (hWlow : mediatorCompression n r W = 0) :
    mediatorFullBottom n r (routingHamiltonian n r Delta C W) =
      Perturbation.lowBlockBottom (actualMediatorLowBlock n r C)
        (diagonalPenalty (actualMediatorWeight n r Delta))
        (routingHighBlock n r C W)
        (routingCoupling n r W) := by
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
    rw [← routingHamiltonian_form_blocks n r Delta C hC W hW hWlow,
      ← assembleMediator_norm_sq, hassemble]
  · rintro ⟨p, q, hpq, rfl⟩
    refine ⟨assembleMediator n r p q, ?_, ?_⟩
    · rw [assembleMediator_norm_sq]
      exact hpq
    · rw [routingHamiltonian_form_blocks n r Delta C hC W hW hWlow,
        assembleMediator_norm_sq]
      rfl

theorem routing_effectiveBottom_matrix (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (W : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ)
    (hW : W.conjTranspose = W) (hWlow : mediatorCompression n r W = 0) :
    Perturbation.effectiveBottom (actualMediatorLowBlock n r C)
      (diagonalPenalty (fun s => (actualMediatorWeight n r Delta s)⁻¹))
      (routingCoupling n r W) =
      sourceMatrixBottom n (C - mediatorCompression n r
        (W * liftedMediatorInverse n r Delta *
          W)) := by
  unfold Perturbation.effectiveBottom sourceMatrixBottom
  simp_rw [routing_effectiveForm n r Delta C W hW hWlow]

theorem routing_bottom (n r : ℕ) {Delta : ℝ} (hDelta : 0 < Delta)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (W : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ)
    (hW : W.conjTranspose = W) (hWlow : mediatorCompression n r W = 0)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 4)
    (hbound : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      ‖spinMatrixOperator W‖ ≤ epsilon * (4 * Delta)) :
    |mediatorFullBottom n r (routingHamiltonian n r Delta C W) -
      sourceMatrixBottom n (C - mediatorCompression n r
        (W * liftedMediatorInverse n r Delta * W))| ≤ 16 * Delta * epsilon ^ 3 := by
  have h := routing_second_order n r hDelta C W hepsilon hsmall hbound
  rw [← routingFullBottom_eq_lowBlockBottom n r Delta C hC W hW hWlow,
    routing_effectiveBottom_matrix n r Delta C W hW hWlow] at h
  exact h

end ContinuumCoulomb

end

end OAI
