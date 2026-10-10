import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexAdjointWeights
import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicAdjointHeight

namespace OAI

/-! # Complex matrix coordinates for the intrinsic adjoint representation -/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped TensorProduct Manifold Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {m n : ℕ}

def complexMatrixExtension (b : Basis (Fin m) ℝ L)
    (c : Basis (Fin n) ℂ (ℂ ⊗[ℝ] L)) :
    Matrix (Fin m) (Fin m) ℝ →ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  ((LinearMap.toMatrixAlgEquiv c).restrictScalars ℝ).toAlgHom.comp
    (((LinearMap.toMatrixAlgEquiv (b.baseChange ℂ)).symm.restrictScalars ℝ).toAlgHom.comp
      (Algebra.ofId ℝ ℂ).mapMatrix)

theorem complexMatrixExtension_ad (b : Basis (Fin m) ℝ L)
    (c : Basis (Fin n) ℂ (ℂ ⊗[ℝ] L)) (x : L) :
    complexMatrixExtension b c (LinearMap.toMatrix b b (LieAlgebra.ad ℝ L x)) =
      complexifiedAdjointMatrix L c x := by
  have hmat : (Algebra.ofId ℝ ℂ).mapMatrix
      (LinearMap.toMatrix b b (LieAlgebra.ad ℝ L x)) =
      LinearMap.toMatrix (b.baseChange ℂ) (b.baseChange ℂ)
        (LieAlgebra.ad ℂ (ℂ ⊗[ℝ] L) ((complexificationLieHom L) x)) := by
    ext i j
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply,
      Basis.baseChange_apply]
    change _ = (b.baseChange ℂ).repr ⁅(1 : ℂ) ⊗ₜ[ℝ] x, (1 : ℂ) ⊗ₜ[ℝ] b j⁆ i
    simp
  change (LinearMap.toMatrixAlgEquiv c)
    ((LinearMap.toMatrixAlgEquiv (b.baseChange ℂ)).symm
      ((Algebra.ofId ℝ ℂ).mapMatrix _)) = _
  rw [hmat]
  exact congrArg (LinearMap.toMatrixAlgEquiv c)
    ((LinearMap.toMatrixAlgEquiv (b.baseChange ℂ)).symm_apply_apply _)

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

def complexAdjointMatrixHom
    (b : Basis (Fin m) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (c : Basis (Fin n) ℂ (ℂ ⊗[ℝ] GroupLieAlgebra (𝓘(ℝ, E)) G)) :
    G →* Matrix (Fin n) (Fin n) ℂ :=
  (complexMatrixExtension b c).toMonoidHom.comp (adjointMatrixHom b)

omit [T2Space G] in
theorem continuous_complexAdjointMatrixHom
    (b : Basis (Fin m) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (c : Basis (Fin n) ℂ (ℂ ⊗[ℝ] GroupLieAlgebra (𝓘(ℝ, E)) G)) :
    Continuous (complexAdjointMatrixHom b c) :=
  (complexMatrixExtension b c).toLinearMap.continuous_of_finiteDimensional.comp
    (continuous_adjointMatrixHom b)

omit [T2Space G] in
theorem complexAdjointMatrixHom_exp
    (b : Basis (Fin m) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    (c : Basis (Fin n) ℂ (ℂ ⊗[ℝ] GroupLieAlgebra (𝓘(ℝ, E)) G))
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (x : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    complexAdjointMatrixHom b c (Exp x) = NormedSpace.exp (complexifiedAdjointMatrix _ c x) := by
  let F := complexMatrixExtension b c
  let : NormedAlgebra ℚ (Matrix (Fin m) (Fin m) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  let : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  change F (adjointMatrixHom b (Exp x)) = _
  rw [adjointMatrixHom_exp_intrinsic b hExp]
  have hm := NormedSpace.map_exp F.toRingHom F.toLinearMap.continuous_of_finiteDimensional
    (LinearMap.toMatrix b b (LieAlgebra.ad ℝ _ x))
  exact hm.trans (congrArg NormedSpace.exp (complexMatrixExtension_ad b c x))

end PolycyclicRecognition

end

end OAI
