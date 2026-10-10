import OAI.GroupTheory.PolycyclicRecognition.Geometry.AdjointExponentialRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularMatrixExponential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularHeight

namespace OAI

/-! # Logarithmic diagonal characters of the actual adjoint action -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator

def matrixLogDiagonalHom {G : Type*} [Group G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℝ)
    (hupper : ∀ g, (ρ g).IsUpperTriangular) (hpos : ∀ g i, 0 < ρ g i i) :
    G →* Multiplicative (Fin n → ℝ) where
  toFun g := Multiplicative.ofAdd (fun i => Real.log (ρ g i i))
  map_one' := by
    apply Multiplicative.ext
    funext i
    simp
  map_mul' g h := by
    apply Multiplicative.ext
    funext i
    change Real.log (ρ (g * h) i i) = Real.log (ρ g i i) + Real.log (ρ h i i)
    rw [map_mul, triangular_mul_diag _ _ (hupper g) (hupper h),
      Real.log_mul (hpos g i).ne' (hpos h i).ne']

@[simp] theorem matrixLogDiagonalHom_apply {G : Type*} [Group G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℝ) (hupper) (hpos) (g : G) (i : Fin n) :
    (matrixLogDiagonalHom ρ hupper hpos g).toAdd i = Real.log (ρ g i i) := rfl

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

def adjointMatrixHom {n : ℕ} (b : Module.Basis (Fin n) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) :
    G →* Matrix (Fin n) (Fin n) ℝ :=
  (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp
    (ContinuousLinearMap.toLinearMapRingHom.toMonoidHom.comp conjugationDifferentialHom)

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

theorem adjointMatrixHom_exp {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G))
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ)
    (hρ : Function.Injective ρ) (hρExp : ∀ x, ρ (Exp x) = algebraExpUnit (j x))
    (x : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    adjointMatrixHom b (Exp x) =
      NormedSpace.exp (LinearMap.toMatrix b b (LieAlgebra.ad ℝ _ x)) := by
  change LinearMap.toMatrix b b ((conjugationDifferentialHom (Exp x)).toLinearMap) = _
  rw [conjugationDifferential_exp hExp j ρ hρ hρExp, toMatrix_adjointExponentialLinear]

theorem adjointMatrixHom_upper {n : ℕ}
    (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) n)
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (hsurj : Function.Surjective Exp)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ)
    (hρ : Function.Injective ρ) (hρExp : ∀ x, ρ (Exp x) = algebraExpUnit (j x))
    (g : G) : (adjointMatrixHom T.basis g).IsUpperTriangular := by
  obtain ⟨x, rfl⟩ := hsurj g
  rw [adjointMatrixHom_exp T.basis hExp j ρ hρ hρExp]
  exact matrix_exp_upperTriangular _ (T.upper x)

theorem adjointMatrixHom_exp_diagonal {n : ℕ}
    (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) n)
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ)
    (hρ : Function.Injective ρ) (hρExp : ∀ x, ρ (Exp x) = algebraExpUnit (j x))
    (x : GroupLieAlgebra (𝓘(ℝ, E)) G) (i : Fin n) :
    adjointMatrixHom T.basis (Exp x) i i = Real.exp (T.character i x) := by
  rw [adjointMatrixHom_exp T.basis hExp j ρ hρ hρExp,
    matrix_exp_diagonal _ (T.upper x), T.character_eq_diag]

/-- The actual adjoint diagonal integrates exactly the canonical height
characters, using the already required representation and exponential chart. -/
def adjointCharacterHom {n : ℕ}
    (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) n)
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (hsurj : Function.Surjective Exp)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ)
    (hρ : Function.Injective ρ) (hρExp : ∀ x, ρ (Exp x) = algebraExpUnit (j x)) :
    G →* Multiplicative (Fin n → ℝ) :=
  matrixLogDiagonalHom (adjointMatrixHom T.basis)
    (adjointMatrixHom_upper T hExp hsurj j ρ hρ hρExp)
    (by
      intro g i
      obtain ⟨x, rfl⟩ := hsurj g
      rw [adjointMatrixHom_exp_diagonal T hExp j ρ hρ hρExp]
      exact Real.exp_pos _)

theorem adjointCharacterHom_exp {n : ℕ}
    (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) n)
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (hsurj : Function.Surjective Exp)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ)
    (hρ : Function.Injective ρ) (hρExp : ∀ x, ρ (Exp x) = algebraExpUnit (j x))
    (x : GroupLieAlgebra (𝓘(ℝ, E)) G) (i : Fin n) :
    (adjointCharacterHom T hExp hsurj j ρ hρ hρExp (Exp x)).toAdd i = T.character i x := by
  change Real.log (adjointMatrixHom T.basis (Exp x) i i) = _
  rw [adjointMatrixHom_exp_diagonal T hExp j ρ hρ hρExp, Real.log_exp]

end PolycyclicRecognition

end

end OAI
