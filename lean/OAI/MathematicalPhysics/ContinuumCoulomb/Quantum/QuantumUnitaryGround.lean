import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGroundComparison

namespace OAI

/-! Exact unitary changes of basis preserve the actual finite ground energy. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped InnerProductSpace
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem qmaUnitary_sandwich_form (U H : Matrix σ σ ℂ) (x : EuclideanSpace ℂ σ) :
    ⟪x,spinMatrixOperator (U.conjTranspose*H*U) x⟫_ℝ =
      ⟪spinMatrixOperator U x,spinMatrixOperator H (spinMatrixOperator U x)⟫_ℝ := by
  simpa only [qmaQuadratic_operator,qmaMatrixOperator_square] using qmaQuadratic_sandwich U H x

theorem qmaNormalizedBottom_unitary (U H : Matrix σ σ ℂ)
    (hU : U.conjTranspose*U = 1) (hU' : U*U.conjTranspose = 1) :
    MediatorGraph.normalizedBottom (U.conjTranspose*H*U) = MediatorGraph.normalizedBottom H := by
  have hnorm := spinMatrixOperator_unitary_norm_map U hU
  have hnorm' := spinMatrixOperator_unitary_norm_map U.conjTranspose
    (by simpa only [Matrix.conjTranspose_conjTranspose] using hU')
  have hinv (x : EuclideanSpace ℂ σ) :
      spinMatrixOperator U (spinMatrixOperator U.conjTranspose x) = x := by
    have hm := congrArg (fun M : Matrix σ σ ℂ => spinMatrixOperator M x) hU'
    simpa only [spinMatrixOperator_mul,ContinuousLinearMap.comp_apply,
      spinMatrixOperator_one,one_apply_eq_self] using hm
  unfold MediatorGraph.normalizedBottom
  congr 1
  ext e
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨spinMatrixOperator U x,(hnorm x).trans hx,qmaUnitary_sandwich_form U H x⟩
  · rintro ⟨x,hx,rfl⟩
    refine ⟨spinMatrixOperator U.conjTranspose x,(hnorm' x).trans hx,?_⟩
    rw [qmaUnitary_sandwich_form,hinv]

end ContinuumCoulomb

end

end OAI
