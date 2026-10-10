import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOperatorQuadratic
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorGraph

namespace OAI

/-! Operator-norm perturbations of the actual finite spin ground energy. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped InnerProductSpace
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem qmaQuadratic_norm_bound (M : Matrix σ σ ℂ) (x : EuclideanSpace ℂ σ) :
    |qmaQuadratic M (fun i => x i)| ≤ ‖spinMatrixOperator M‖*‖x‖^2 := by
  rw [qmaQuadratic_operator,qmaMatrixOperator_square]
  calc
    _ ≤ ‖x‖*‖spinMatrixOperator M x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖*(‖spinMatrixOperator M‖*‖x‖) :=
      mul_le_mul_of_nonneg_left ((spinMatrixOperator M).le_opNorm x) (norm_nonneg x)
    _ = _ := by ring

theorem qmaNormalizedBottom_bddBelow (M : Matrix σ σ ℂ) :
    BddBelow {e | ∃ x : EuclideanSpace ℂ σ, ‖x‖ = 1 ∧
      e = ⟪x,spinMatrixOperator M x⟫_ℝ} := by
  refine ⟨-‖spinMatrixOperator M‖,?_⟩
  rintro e ⟨x,hx,rfl⟩
  have h := (abs_le.mp (qmaQuadratic_norm_bound M x)).1
  simpa only [hx,one_pow,mul_one,qmaQuadratic_operator,qmaMatrixOperator_square] using h

theorem qmaNormalizedBottom_le (M : Matrix σ σ ℂ) (x : EuclideanSpace ℂ σ)
    (hx : ‖x‖ = 1) :
    MediatorGraph.normalizedBottom M ≤ qmaQuadratic M (fun i => x i) := by
  rw [qmaQuadratic_operator,qmaMatrixOperator_square]
  exact csInf_le (qmaNormalizedBottom_bddBelow M) ⟨x,hx,rfl⟩

theorem le_qmaNormalizedBottom (M : Matrix σ σ ℂ) (u : EuclideanSpace ℂ σ)
    (hu : ‖u‖ = 1) {b : ℝ}
    (h : ∀ x : EuclideanSpace ℂ σ, ‖x‖ = 1 → b ≤ qmaQuadratic M (fun i => x i)) :
    b ≤ MediatorGraph.normalizedBottom M := by
  apply le_csInf (show {e | ∃ x : EuclideanSpace ℂ σ, ‖x‖ = 1 ∧
    e = ⟪x,spinMatrixOperator M x⟫_ℝ}.Nonempty from ⟨_,u,hu,rfl⟩)
  rintro e ⟨x,hx,rfl⟩
  simpa only [qmaQuadratic_operator,qmaMatrixOperator_square] using h x hx

theorem qmaNormalizedBottom_error (M N : Matrix σ σ ℂ)
    (u : EuclideanSpace ℂ σ) (hu : ‖u‖ = 1) {δ : ℝ}
    (herror : ∀ x : EuclideanSpace ℂ σ, ‖x‖ = 1 →
      |qmaQuadratic M (fun i => x i)-qmaQuadratic N (fun i => x i)| ≤ δ) :
    |MediatorGraph.normalizedBottom M-MediatorGraph.normalizedBottom N| ≤ δ := by
  have hMN : MediatorGraph.normalizedBottom N-δ ≤ MediatorGraph.normalizedBottom M := by
    apply le_qmaNormalizedBottom M u hu
    intro x hx
    have hN := qmaNormalizedBottom_le N x hx
    have he := (abs_le.mp (herror x hx)).1
    linarith
  have hNM : MediatorGraph.normalizedBottom M-δ ≤ MediatorGraph.normalizedBottom N := by
    apply le_qmaNormalizedBottom N u hu
    intro x hx
    have hM := qmaNormalizedBottom_le M x hx
    have he := (abs_le.mp (herror x hx)).2
    linarith
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem qmaNormalizedBottom_norm_error (M N : Matrix σ σ ℂ)
    (u : EuclideanSpace ℂ σ) (hu : ‖u‖ = 1) {δ : ℝ}
    (herror : ‖spinMatrixOperator (M-N)‖ ≤ δ) :
    |MediatorGraph.normalizedBottom M-MediatorGraph.normalizedBottom N| ≤ δ := by
  apply qmaNormalizedBottom_error M N u hu
  intro x hx
  rw [← qmaQuadratic_sub]
  have h := (qmaQuadratic_norm_bound (M-N) x).trans
    (mul_le_mul_of_nonneg_right herror (sq_nonneg ‖x‖))
  simpa only [hx,one_pow,mul_one] using h

end ContinuumCoulomb

end

end OAI
