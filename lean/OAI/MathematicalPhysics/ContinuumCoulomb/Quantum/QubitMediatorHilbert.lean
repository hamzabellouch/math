import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitMediatorPenalty
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.OrthogonalBlockDecomposition

namespace OAI

/-! Actual Hilbert-space low and complementary coordinates for qubit mediators. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

def qmaMediatorInclusion : EuclideanSpace ℂ σ →L[ℝ] EuclideanSpace ℂ (σ × (κ → Fin 2)) :=
  (qmaMatrixOperator qmaMediatorVacuumColumn).restrictScalars ℝ

def qmaMediatorRestriction : EuclideanSpace ℂ (σ × (κ → Fin 2)) →L[ℝ] EuclideanSpace ℂ σ :=
  (qmaMatrixOperator (qmaMediatorVacuumColumn (σ := σ) (κ := κ)).conjTranspose).restrictScalars ℝ

def qmaMediatorHighProjection : EuclideanSpace ℂ (σ × (κ → Fin 2)) →L[ℝ]
    EuclideanSpace ℂ (σ × (κ → Fin 2)) :=
  (spinMatrixOperator qmaMediatorHighMatrix).restrictScalars ℝ

theorem qmaMediator_restrict_include (p : EuclideanSpace ℂ σ) :
    qmaMediatorRestriction (κ := κ) (qmaMediatorInclusion p) = p := by
  change qmaMatrixOperator _ (qmaMatrixOperator _ p) = p
  rw [← ContinuousLinearMap.comp_apply,← qmaMatrixOperator_mul,qmaMediatorVacuum_gram,
    qmaMatrixOperator_square,spinMatrixOperator_one]
  rfl

theorem qmaMediator_inclusion_adjoint (p : EuclideanSpace ℂ σ)
    (x : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
    ⟪qmaMediatorInclusion p,x⟫_ℝ = ⟪p,qmaMediatorRestriction x⟫_ℝ := by
  have h := ContinuousLinearMap.adjoint_inner_right
    (qmaMatrixOperator (qmaMediatorVacuumColumn (σ := σ) (κ := κ))) p x
  rw [← qmaMatrixOperator_star] at h
  rw [qmaEuclidean_real_inner,qmaEuclidean_real_inner]
  exact congrArg Complex.re h.symm

theorem qmaMediator_highPart (x : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
    Perturbation.orthogonalHighPart qmaMediatorInclusion qmaMediatorRestriction x =
      qmaMediatorHighProjection x := by
  have hm := qmaMediator_projection_sum (σ := σ) (κ := κ)
  have h := congrArg (fun M => qmaMatrixOperator M x) hm
  rw [qmaMatrixOperator_add,qmaMatrixOperator_mul] at h
  simp only [qmaMatrixOperator_square,spinMatrixOperator_one] at h
  change qmaMediatorInclusion (qmaMediatorRestriction x)+qmaMediatorHighProjection x = x at h
  unfold Perturbation.orthogonalHighPart
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using h.symm)

theorem qmaMediator_norm_decomposition (x : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
    ‖qmaMediatorRestriction x‖^2+‖qmaMediatorHighProjection x‖^2 = ‖x‖^2 := by
  rw [← qmaMediator_highPart]
  exact Perturbation.orthogonalParts_norm qmaMediatorInclusion qmaMediatorRestriction
    qmaMediator_restrict_include qmaMediator_inclusion_adjoint x

theorem qmaMediatorHighProjection_norm :
    ‖qmaMediatorHighProjection (σ := σ) (κ := κ)‖ ≤ 1 := by
  rw [qmaMediatorHighProjection,ContinuousLinearMap.norm_restrictScalars]
  exact qmaMediatorHigh_norm

theorem qmaMediatorRestriction_high (x : EuclideanSpace ℂ (σ × (κ → Fin 2))) :
    qmaMediatorRestriction (qmaMediatorHighProjection x) = 0 := by
  change qmaMatrixOperator _ (qmaMatrixOperator _ x) = 0
  rw [← ContinuousLinearMap.comp_apply,← qmaMatrixOperator_mul,qmaMediatorVacuum_high]
  ext p
  simp [qmaMatrixOperator_apply]

theorem qmaMediatorRestriction_column (V : κ → Matrix σ σ ℂ) (p : EuclideanSpace ℂ σ) :
    qmaMediatorRestriction (qmaMatrixOperator (qmaAncillaColumn V) p) = 0 := by
  have hQ := congrArg (fun M => qmaMatrixOperator M p) (qmaMediatorHigh_column V)
  rw [qmaMatrixOperator_mul] at hQ
  change qmaMediatorHighProjection (qmaMatrixOperator (qmaAncillaColumn V) p) =
    qmaMatrixOperator (qmaAncillaColumn V) p at hQ
  rw [← hQ]
  exact qmaMediatorRestriction_high _

end ContinuumCoulomb

end

end OAI
