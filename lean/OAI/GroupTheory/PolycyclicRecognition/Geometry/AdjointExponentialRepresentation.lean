import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialTangentUniqueness
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GeneratorConjugation
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

namespace OAI

/-! # Identifying the actual adjoint exponential through a faithful representation -/

noncomputable section
namespace PolycyclicRecognition

section Algebra

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

local instance adjointExponentialNormedAddCommGroup : NormedAddCommGroup L :=
  generatorConjugationNormedAddCommGroup
local instance adjointExponentialNormedSpace : NormedSpace ℝ L := generatorConjugationNormedSpace

open scoped Matrix.Norms.Operator

/-- The algebraic endomorphism underlying the analytic exponential of `ad x`.
The auxiliary finite-dimensional norm is not part of the output. -/
def adjointExponentialLinear (x : L) : L →ₗ[ℝ] L :=
  (NormedSpace.exp (continuousAd x)).toLinearMap

theorem toMatrix_adjointExponentialLinear {n : ℕ} (b : Module.Basis (Fin n) ℝ L) (x : L) :
    LinearMap.toMatrix b b (adjointExponentialLinear x) =
      NormedSpace.exp (LinearMap.toMatrix b b (LieAlgebra.ad ℝ L x)) := by
  let f : (L →L[ℝ] L) →+* Matrix (Fin n) (Fin n) ℝ :=
    (LinearMap.toMatrixAlgEquiv b).toRingHom.comp ContinuousLinearMap.toLinearMapRingHom
  let fL : (L →L[ℝ] L) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    (LinearMap.toMatrix b b).toLinearMap.comp (ContinuousLinearMap.coeLM ℝ)
  have hf : Continuous f := fL.continuous_of_finiteDimensional
  let : NormedAlgebra ℚ (L →L[ℝ] L) := NormedAlgebra.restrictScalars ℚ ℝ _
  let : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have h := NormedSpace.map_exp f hf (continuousAd x)
  exact h

variable {G : Type*} [Group G]
  {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

theorem exp_adjointExponentialLinear
    (Exp : L → G) (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (hExp : ∀ x, ρ (Exp x) = algebraExpUnit (j x)) (x v : L) :
    Exp (adjointExponentialLinear x v) = Exp x * Exp v * (Exp x)⁻¹ := by
  change Exp (NormedSpace.exp (continuousAd x) v) = _
  simpa only [one_smul] using exp_ad_eq_group_conjugation Exp j ρ hρ hExp x v 1

end Algebra

section LieGroup

open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]
  {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Faithful exponential compatibility identifies the actual tangent
adjoint action with the algebraic adjoint exponential. -/
theorem conjugationDifferential_exp
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ)
    (hρ : Function.Injective ρ) (hρExp : ∀ x, ρ (Exp x) = algebraExpUnit (j x))
    (x : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    (conjugationDifferentialHom (Exp x)).toLinearMap = adjointExponentialLinear x := by
  ext v
  exact conjugationDifferential_eq_of_exponential hExp (Exp x)
    (adjointExponentialLinear x) (exp_adjointExponentialLinear Exp j ρ hρ hρExp x) v

end LieGroup
end PolycyclicRecognition

end

end OAI
