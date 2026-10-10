import OAI.GroupTheory.PolycyclicRecognition.Geometry.DerivationFlowRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicAdjointExponential

namespace OAI

/-! # Nilpotent derivation flow in any Lie group -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

theorem derivationFlow_intrinsic_adjoint
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (f : L →ₗ[ℝ] GroupLieAlgebra (𝓘(ℝ, E)) G) (u : GroupLieAlgebra (𝓘(ℝ, E)) G)
    (hf : ∀ x, f (D x) = ⁅u, f x⁆) (t : ℝ) (x : L) :
    f (nilpotentDerivationFlow D hD t x) =
      conjugationDifferentialHom (E := E) (Exp (t • u)) (f x) := by
  let fE : L →ₗ[ℝ] E := f
  rw [nilpotentDerivationFlow_eq_analytic]
  have he := exp_intertwine_apply fE.toContinuousLinearMap
    (t • D.toLinearMap.toContinuousLinearMap) (t • groupAdjointOperator (E := E) u)
    (by
      intro y
      change f (t • D y) = t • ⁅u, f y⁆
      rw [map_smul, hf]) x
  rw [← adjointLinearMap_exponential hExp u t] at he
  exact he

theorem derivationFlow_intrinsic_conjugation [T2Space G]
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (f : L →ₗ[ℝ] GroupLieAlgebra (𝓘(ℝ, E)) G) (u : GroupLieAlgebra (𝓘(ℝ, E)) G)
    (hf : ∀ x, f (D x) = ⁅u, f x⁆) (t : ℝ) (x : L) :
    Exp (f (nilpotentDerivationFlow D hD t x)) =
      Exp (t • u) * Exp (f x) * (Exp (t • u))⁻¹ := by
  rw [derivationFlow_intrinsic_adjoint D hD Exp hExp f u hf]
  exact (conjugation_exponential hExp (Exp (t • u)) (f x)).symm

end PolycyclicRecognition

end

end OAI
