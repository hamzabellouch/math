import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitMediatorForms

namespace OAI

/-! Norm bounds for arbitrary old-spin operators tensored with the actual
mediator identity, occupation projections, and flips. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {σ α κ : Type*} [Fintype σ] [DecidableEq σ]
  [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]

theorem qmaKronecker_identity_apply (M : Matrix σ σ ℂ)
    (x : EuclideanSpace ℂ (σ × α)) (s : σ) (a : α) :
    spinMatrixOperator (M ⊗ₖ (1 : Matrix α α ℂ)) x (s,a) =
      spinMatrixOperator M (WithLp.toLp 2 (fun t => x (t,a))) s := by
  simp [spinMatrixOperator_apply,Matrix.one_apply,
    Fintype.sum_prod_type]

theorem qmaKronecker_identity_norm (M : Matrix σ σ ℂ) :
    ‖spinMatrixOperator (M ⊗ₖ (1 : Matrix α α ℂ))‖ ≤ ‖spinMatrixOperator M‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow]
  simp only [EuclideanSpace.norm_sq_eq,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ a : α, ‖spinMatrixOperator M‖^2*(∑ s : σ, ‖x (s,a)‖^2) := by
      apply Finset.sum_le_sum
      intro a _
      let y : EuclideanSpace ℂ σ := WithLp.toLp 2 (fun t => x (t,a))
      have h := pow_le_pow_left₀ (norm_nonneg _) ((spinMatrixOperator M).le_opNorm y) 2
      simpa only [mul_pow,EuclideanSpace.norm_sq_eq,qmaKronecker_identity_apply,y] using h
    _ = _ := by rw [← Finset.mul_sum,Finset.sum_comm]

theorem qmaKronecker_flip_norm (M : Matrix σ σ ℂ) (e : κ) :
    ‖spinMatrixOperator (M ⊗ₖ qmaBitFlipMatrix e)‖ ≤ ‖spinMatrixOperator M‖ := by
  have hfac : M ⊗ₖ qmaBitFlipMatrix e =
      (M ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ))*
        ((1 : Matrix σ σ ℂ) ⊗ₖ qmaBitFlipMatrix e) := by
    rw [← Matrix.mul_kronecker_mul,mul_one,one_mul]
  rw [hfac,spinMatrixOperator_mul]
  have hflip : ‖spinMatrixOperator ((1 : Matrix σ σ ℂ) ⊗ₖ qmaBitFlipMatrix e)‖ ≤ 1 := by
    apply qmaKronecker_unitary_norm
    · simp
    · rw [qmaBitFlipMatrix_star,qmaBitFlipMatrix_square]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (qmaKronecker_identity_norm M) hflip (norm_nonneg _) (norm_nonneg _)).trans_eq
      (mul_one _))

theorem qmaKronecker_occupation_norm_bound (M : Matrix σ σ ℂ) (e : κ) :
    ‖spinMatrixOperator (M ⊗ₖ qmaAncillaOccupation e)‖ ≤ ‖spinMatrixOperator M‖ := by
  have hfac : M ⊗ₖ qmaAncillaOccupation e =
      (M ⊗ₖ (1 : Matrix (κ → Fin 2) (κ → Fin 2) ℂ))*
        ((1 : Matrix σ σ ℂ) ⊗ₖ qmaAncillaOccupation e) := by
    rw [← Matrix.mul_kronecker_mul,mul_one,one_mul]
  rw [hfac,spinMatrixOperator_mul]
  have hocc : ‖spinMatrixOperator ((1 : Matrix σ σ ℂ) ⊗ₖ qmaAncillaOccupation e)‖ ≤ 1 :=
    qmaKronecker_occupation_norm _ (by simp) e
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (qmaKronecker_identity_norm M) hocc (norm_nonneg _) (norm_nonneg _)).trans_eq
      (mul_one _))

theorem qmaPerturbationOperator_norm (C : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ) :
    ‖qmaPerturbationOperator C D V‖ ≤ ‖spinMatrixOperator C‖+
      ∑ e, ‖spinMatrixOperator (D e)‖+∑ e, ‖spinMatrixOperator (V e)‖ := by
  change ‖(qmaMatrixOperator (qmaMediatorPerturbation C D V)).restrictScalars ℝ‖ ≤ _
  rw [ContinuousLinearMap.norm_restrictScalars,qmaMatrixOperator_square]
  unfold qmaMediatorPerturbation qmaMediatorOccupations qmaMediatorFlips
  simp only [spinMatrixOperator_add,spinMatrixOperator_sum]
  have hD : ‖∑ e, spinMatrixOperator (D e ⊗ₖ qmaAncillaOccupation e)‖ ≤
      ∑ e, ‖spinMatrixOperator (D e)‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun e _ => qmaKronecker_occupation_norm_bound _ e))
  have hV : ‖∑ e, spinMatrixOperator (V e ⊗ₖ qmaBitFlipMatrix e)‖ ≤
      ∑ e, ‖spinMatrixOperator (V e)‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun e _ => qmaKronecker_flip_norm _ e))
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add (qmaKronecker_identity_norm C) hD)) hV)

end ContinuumCoulomb

end

end OAI
