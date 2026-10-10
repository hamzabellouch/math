import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorForms

namespace OAI

/-! Low and high blocks for the finite singlet stars used in lattice routing. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

def routingCoupling (n r : ℕ)
    (W : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ) :
    MediatorLowSpace n →L[ℝ] MediatorHighSpace n r :=
  ((mediatorHighRestriction n r).comp
    ((spinMatrixOperator W).comp (mediatorLowInclusion n r))).restrictScalars ℝ

def routingHighBlock (n r : ℕ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (W : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ) :
    MediatorHighSpace n r →L[ℝ] MediatorHighSpace n r :=
  ((mediatorHighRestriction n r).comp
    ((spinMatrixOperator (C ⊗ₖ 1 + W)).comp
      (mediatorHighInclusion n r))).restrictScalars ℝ

theorem routingCoupling_norm (n r : ℕ)
    (W : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ) :
    ‖routingCoupling n r W‖ ≤ ‖spinMatrixOperator W‖ := by
  unfold routingCoupling
  rw [ContinuousLinearMap.norm_restrictScalars]
  exact HubbardGlobal.coordinateCompression_norm _ _ _
    (mediatorHighRestriction_norm n r) (mediatorLowInclusion_norm n r)

theorem routingHighBlock_norm (n r : ℕ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (W : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ) :
    ‖routingHighBlock n r C W‖ ≤
      ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      ‖spinMatrixOperator W‖ := by
  unfold routingHighBlock
  rw [ContinuousLinearMap.norm_restrictScalars]
  exact (HubbardGlobal.coordinateCompression_norm _ _ _
    (mediatorHighRestriction_norm n r) (mediatorHighInclusion_norm n r)).trans
      (spinMatrixOperator_add_norm_bound _ _ _ le_rfl)

theorem routing_second_order (n r : ℕ) {Delta : ℝ} (hDelta : 0 < Delta)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (W : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 4)
    (hbound : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      ‖spinMatrixOperator W‖ ≤ epsilon * (4 * Delta)) :
    |Perturbation.lowBlockBottom (actualMediatorLowBlock n r C)
        (diagonalPenalty (actualMediatorWeight n r Delta))
        (routingHighBlock n r C W) (routingCoupling n r W) -
      Perturbation.effectiveBottom (actualMediatorLowBlock n r C)
        (diagonalPenalty (fun s => (actualMediatorWeight n r Delta s)⁻¹))
        (routingCoupling n r W)| ≤ 16 * Delta * epsilon ^ 3 := by
  obtain ⟨hAT, hT, hgap⟩ := actualMediator_inverse_data n r hDelta
  have hg : 0 < 4 * Delta := by positivity
  have hB : ‖routingCoupling n r W‖ ≤ epsilon * (4 * Delta) :=
    (routingCoupling_norm n r W).trans
      ((le_add_of_nonneg_left (norm_nonneg _)).trans hbound)
  have hC : ‖actualMediatorLowBlock n r C‖ ≤ epsilon * (4 * Delta) :=
    (actualMediatorLowBlock_norm n r C).trans
      ((le_add_of_nonneg_right (norm_nonneg _)).trans hbound)
  have hD := (routingHighBlock_norm n r C W).trans hbound
  have hu : ‖(EuclideanSpace.single (fun _ : Fin n => (0 : Fin 2)) (1 : ℂ) :
      MediatorLowSpace n)‖ = 1 := by simp
  convert Perturbation.finite_lowBlockBottom_second_order
    (actualMediatorLowBlock n r C) (diagonalPenalty (actualMediatorWeight n r Delta))
    (diagonalPenalty (fun s => (actualMediatorWeight n r Delta s)⁻¹))
    (routingHighBlock n r C W) (routingCoupling n r W)
    hg hepsilon hsmall hAT (diagonalPenalty_symmetric _)
    (fun q => (mul_nonneg hg.le (sq_nonneg ‖q‖)).trans (hgap q)) hgap hT hB hC hD _ hu using 1
  ring

end ContinuumCoulomb

end

end OAI
