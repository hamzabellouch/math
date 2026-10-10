import OAI.Probability.InvariantIsing.Haar.Rotation
import OAI.Probability.InvariantIsing.Haar.HaarDerivative
import OAI.Probability.InvariantIsing.Haar.PublishedInputs

namespace OAI

/-! Relating the orthogonal matrix and Euclidean-isometry models. -/

noncomputable section

open scoped BigOperators Matrix

namespace InvariantIsing

lemma orthogonal_mulVec_norm_sq {N : ℕ} (U : Orthogonal N)
    (v : EuclideanSpace ℝ (Fin N)) :
    ‖WithLp.toLp 2 ((U : Matrix (Fin N) (Fin N) ℝ) *ᵥ v.ofLp)‖ ^ 2 = ‖v‖ ^ 2 := by
  have hU : (U : Matrix (Fin N) (Fin N) ℝ)ᵀ *
      (U : Matrix (Fin N) (Fin N) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp U.property
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [pow_two]
  change ((U : Matrix (Fin N) (Fin N) ℝ) *ᵥ v.ofLp) ⬝ᵥ
      ((U : Matrix (Fin N) (Fin N) ℝ) *ᵥ v.ofLp) = v.ofLp ⬝ᵥ v.ofLp
  rw [← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, hU,
    Matrix.one_mulVec]

/-- An orthogonal matrix acts as a linear isometry in the pressure model. -/
def matrixRotation {N : ℕ} (U : Orthogonal N) : Rotation N :=
  { ((WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).trans
      (Matrix.UnitaryGroup.toLinearEquiv U)).trans
      (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm with
    norm_map' := fun v => (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      (orthogonal_mulVec_norm_sq U v) }

@[simp] lemma matrixRotation_apply {N : ℕ} (U : Orthogonal N)
    (v : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    matrixRotation U v i = ∑ j, (U : Matrix (Fin N) (Fin N) ℝ) i j * v j := rfl

/-- Restricting from O(N) to SO(N) preserves the same spectral action. -/
def specialRotation {N : ℕ} (U : SpecialOrthogonal N) : Rotation N :=
  matrixRotation ⟨U.val, (Matrix.mem_specialOrthogonalGroup_iff.mp U.property).1⟩

@[simp] lemma specialRotation_apply {N : ℕ} (U : SpecialOrthogonal N)
    (v : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    specialRotation U v i = ∑ j, (U : Matrix (Fin N) (Fin N) ℝ) i j * v j := rfl

end InvariantIsing

end

end OAI
