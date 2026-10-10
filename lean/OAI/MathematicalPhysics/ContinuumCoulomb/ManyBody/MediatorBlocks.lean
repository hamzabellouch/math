import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.SpinMatrixNorm
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockBlocks

namespace OAI

/-! Concrete low and high blocks for simultaneous singlet mediators.
The nonzero original-spin block is retained throughout. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace

abbrev MediatorLowSpace (n : ℕ) := EuclideanSpace ℂ (SourceSpinBasis n)
abbrev MediatorHighSpace (n r : ℕ) := EuclideanSpace ℂ (SourceSpinBasis n × MediatorHighBasis r)
abbrev MediatorFullSpace (n r : ℕ) := EuclideanSpace ℂ (MediatedSpinBasis n r)

def mediatorLowIndex (n r : ℕ) (s : SourceSpinBasis n) : MediatedSpinBasis n r :=
  (s, mediatorVacuum r)

def mediatorHighIndex (n r : ℕ) (s : SourceSpinBasis n × MediatorHighBasis r) :
    MediatedSpinBasis n r := (s.1, s.2.val)

theorem mediatorLowIndex_injective (n r : ℕ) : Function.Injective (mediatorLowIndex n r) := by
  intro s t h
  exact congrArg Prod.fst h

theorem mediatorHighIndex_injective (n r : ℕ) : Function.Injective (mediatorHighIndex n r) := by
  rintro ⟨s, a⟩ ⟨t, b⟩ h
  change (s, a.val) = (t, b.val) at h
  have hs : s = t := congrArg (fun x : SourceSpinBasis n × MediatorBasis r => x.1) h
  have ha : a.val = b.val := congrArg (fun x : SourceSpinBasis n × MediatorBasis r => x.2) h
  exact Prod.ext hs (Subtype.ext ha)

def mediatorLowInclusion (n r : ℕ) : MediatorLowSpace n →L[ℂ] MediatorFullSpace n r :=
  HubbardGlobal.coordinateInclusion (mediatorLowIndex n r)

def mediatorLowRestriction (n r : ℕ) : MediatorFullSpace n r →L[ℂ] MediatorLowSpace n :=
  HubbardGlobal.coordinateRestriction (mediatorLowIndex n r)

def mediatorHighInclusion (n r : ℕ) : MediatorHighSpace n r →L[ℂ] MediatorFullSpace n r :=
  HubbardGlobal.coordinateInclusion (mediatorHighIndex n r)

def mediatorHighRestriction (n r : ℕ) : MediatorFullSpace n r →L[ℂ] MediatorHighSpace n r :=
  HubbardGlobal.coordinateRestriction (mediatorHighIndex n r)

theorem mediatorLowInclusion_norm (n r : ℕ) : ‖mediatorLowInclusion n r‖ ≤ 1 :=
  HubbardGlobal.coordinateInclusion_norm_le _ (mediatorLowIndex_injective n r)

theorem mediatorHighInclusion_norm (n r : ℕ) : ‖mediatorHighInclusion n r‖ ≤ 1 :=
  HubbardGlobal.coordinateInclusion_norm_le _ (mediatorHighIndex_injective n r)

theorem mediatorLowRestriction_norm (n r : ℕ) : ‖mediatorLowRestriction n r‖ ≤ 1 :=
  HubbardGlobal.coordinateRestriction_norm_le _ (mediatorLowIndex_injective n r)

theorem mediatorHighRestriction_norm (n r : ℕ) : ‖mediatorHighRestriction n r‖ ≤ 1 :=
  HubbardGlobal.coordinateRestriction_norm_le _ (mediatorHighIndex_injective n r)

def actualMediatorWeight (n r : ℕ) (Delta : ℝ) (s : SourceSpinBasis n × MediatorHighBasis r) : ℝ :=
  mediatorPenaltyWeight r Delta s.2.val

theorem actualMediator_inverse_data (n r : ℕ) {Delta : ℝ} (hDelta : 0 < Delta) :
    (∀ x, diagonalPenalty (actualMediatorWeight n r Delta)
      (diagonalPenalty (fun s => (actualMediatorWeight n r Delta s)⁻¹) x) = x) ∧
    ‖diagonalPenalty (fun s => (actualMediatorWeight n r Delta s)⁻¹)‖ ≤ 1 / (4 * Delta) ∧
    (∀ x, (4 * Delta) * ‖x‖ ^ 2 ≤ ⟪x, diagonalPenalty (actualMediatorWeight n r Delta) x⟫_ℝ) := by
  have hg : 0 < 4 * Delta := by positivity
  have hgap (s : SourceSpinBasis n × MediatorHighBasis r) :
      4 * Delta ≤ actualMediatorWeight n r Delta s := by
    have hcount : (1 : ℝ) ≤ mediatorExcitationNumber r s.2.val := by
      exact_mod_cast mediatorExcitationNumber_pos r s.2.val s.2.property
    simpa only [mul_one, actualMediatorWeight, mediatorPenaltyWeight] using
      mul_le_mul_of_nonneg_left hcount hg.le
  exact ⟨diagonalPenalty_inverse_right _ (fun s => ne_of_gt (hg.trans_le (hgap s))),
    diagonalPenalty_inverse_norm hg _ hgap, diagonalPenalty_gap _ _ hgap⟩

def actualMediatorLowBlock (n r : ℕ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    MediatorLowSpace n →L[ℝ] MediatorLowSpace n :=
  ((mediatorLowRestriction n r).comp
    ((spinMatrixOperator (C ⊗ₖ 1)).comp (mediatorLowInclusion n r))).restrictScalars ℝ

def actualMediatorCoupling (n r : ℕ) (left right : Fin r → Fin n)
    (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    MediatorLowSpace n →L[ℝ] MediatorHighSpace n r :=
  ((mediatorHighRestriction n r).comp
    ((spinMatrixOperator (totalMediatorSpokes n r left right member amplitude)).comp
      (mediatorLowInclusion n r))).restrictScalars ℝ

def actualMediatorHighBlock (n r : ℕ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    MediatorHighSpace n r →L[ℝ] MediatorHighSpace n r :=
  ((mediatorHighRestriction n r).comp
    ((spinMatrixOperator (C ⊗ₖ 1 + totalMediatorSpokes n r left right member amplitude)).comp
      (mediatorHighInclusion n r))).restrictScalars ℝ

theorem actualMediatorLowBlock_norm (n r : ℕ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    ‖actualMediatorLowBlock n r C‖ ≤ ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ := by
  unfold actualMediatorLowBlock
  rw [ContinuousLinearMap.norm_restrictScalars]
  exact HubbardGlobal.coordinateCompression_norm _ _ _
    (mediatorLowRestriction_norm n r) (mediatorLowInclusion_norm n r)

theorem actualMediatorCoupling_norm (n r : ℕ) (left right : Fin r → Fin n)
    (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    ‖actualMediatorCoupling n r left right member amplitude‖ ≤ 6 * ∑ e, |amplitude e| := by
  unfold actualMediatorCoupling
  rw [ContinuousLinearMap.norm_restrictScalars]
  exact (HubbardGlobal.coordinateCompression_norm _ _ _
    (mediatorHighRestriction_norm n r) (mediatorLowInclusion_norm n r)).trans
      (totalMediatorSpokes_operator_norm n r left right member amplitude)

theorem spinMatrixOperator_add_norm_bound {α : Type*} [Fintype α] [DecidableEq α]
    (M N : Matrix α α ℂ) (K : ℝ) (hN : ‖spinMatrixOperator N‖ ≤ K) :
    ‖spinMatrixOperator (M + N)‖ ≤ ‖spinMatrixOperator M‖ + K := by
  rw [spinMatrixOperator_add]
  calc
    ‖spinMatrixOperator M + spinMatrixOperator N‖ ≤
        ‖spinMatrixOperator M‖ + ‖spinMatrixOperator N‖ := norm_add_le _ _
    _ ≤ ‖spinMatrixOperator M‖ + K := by linarith only [hN]

theorem liftedMediatorPerturbation_norm (n r : ℕ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ) +
      totalMediatorSpokes n r left right member amplitude)‖ ≤
      ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ + 6 * ∑ e, |amplitude e| := by
  exact spinMatrixOperator_add_norm_bound _ _ _
    (totalMediatorSpokes_operator_norm n r left right member amplitude)

theorem actualMediatorHighBlock_norm (n r : ℕ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ) :
    ‖actualMediatorHighBlock n r C left right member amplitude‖ ≤
      ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ + 6 * ∑ e, |amplitude e| := by
  unfold actualMediatorHighBlock
  rw [ContinuousLinearMap.norm_restrictScalars]
  exact (HubbardGlobal.coordinateCompression_norm _ _ _
    (mediatorHighRestriction_norm n r) (mediatorHighInclusion_norm n r)).trans
      (liftedMediatorPerturbation_norm n r C left right member amplitude)

/-- A supporting block estimate for the actual simultaneous mediator
construction, retaining the unreplaced low Hamiltonian C. -/
theorem actualMediator_second_order (n r : ℕ) {Delta : ℝ} (hDelta : 0 < Delta)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (left right : Fin r → Fin n) (member : Fin r → Fin 2) (amplitude : Fin r → ℝ)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 4)
    (hbound : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      6 * ∑ e, |amplitude e| ≤ epsilon * (4 * Delta)) :
    |Perturbation.lowBlockBottom (actualMediatorLowBlock n r C)
        (diagonalPenalty (actualMediatorWeight n r Delta))
        (actualMediatorHighBlock n r C left right member amplitude)
        (actualMediatorCoupling n r left right member amplitude) -
      Perturbation.effectiveBottom (actualMediatorLowBlock n r C)
        (diagonalPenalty (fun s => (actualMediatorWeight n r Delta s)⁻¹))
        (actualMediatorCoupling n r left right member amplitude)| ≤ 16 * Delta * epsilon ^ 3 := by
  obtain ⟨hAT, hT, hgap⟩ := actualMediator_inverse_data n r hDelta
  have hg : 0 < 4 * Delta := by positivity
  have hamp : 0 ≤ 6 * ∑ e, |amplitude e| := by positivity
  have hB : ‖actualMediatorCoupling n r left right member amplitude‖ ≤ epsilon * (4 * Delta) :=
    (actualMediatorCoupling_norm n r left right member amplitude).trans
      ((le_add_of_nonneg_left (norm_nonneg _)).trans hbound)
  have hC : ‖actualMediatorLowBlock n r C‖ ≤ epsilon * (4 * Delta) :=
    (actualMediatorLowBlock_norm n r C).trans ((le_add_of_nonneg_right hamp).trans hbound)
  have hD := (actualMediatorHighBlock_norm n r C left right member amplitude).trans hbound
  have hu : ‖(EuclideanSpace.single (fun _ : Fin n => (0 : Fin 2)) (1 : ℂ) : MediatorLowSpace n)‖ = 1 := by
    simp
  convert Perturbation.finite_lowBlockBottom_second_order
    (actualMediatorLowBlock n r C) (diagonalPenalty (actualMediatorWeight n r Delta))
    (diagonalPenalty (fun s => (actualMediatorWeight n r Delta s)⁻¹))
    (actualMediatorHighBlock n r C left right member amplitude)
    (actualMediatorCoupling n r left right member amplitude)
    hg hepsilon hsmall hAT (diagonalPenalty_symmetric _)
    (fun q => (mul_nonneg hg.le (sq_nonneg ‖q‖)).trans (hgap q)) hgap hT hB hC hD _ hu using 1
  ring

end ContinuumCoulomb

end

end OAI
