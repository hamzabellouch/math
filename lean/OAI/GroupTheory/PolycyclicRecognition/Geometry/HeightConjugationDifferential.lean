import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialTangentUniqueness
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialHeightKernel

namespace OAI

/-! # The adjoint action is the identity on the canonical height quotient -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]

def conjugationDifferentialLinearEquiv (g : G) :
    GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₗ[ℝ] GroupLieAlgebra (𝓘(ℝ, E)) G where
  __ := (conjugationDifferentialHom (E := E) g).toLinearMap
  invFun := conjugationDifferentialHom (E := E) g⁻¹
  left_inv v := by
    change (conjugationDifferentialHom (E := E) g⁻¹ *
      conjugationDifferentialHom (E := E) g) v = v
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv v := by
    change (conjugationDifferentialHom (E := E) g *
      conjugationDifferentialHom (E := E) g⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl

variable [T2Space G] [FiniteDimensional ℝ E]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
  (q : HeightSpace T.character ≃ₗ[ℝ] W)
  {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
  (π : G →* Multiplicative W)
  (hπExp : ∀ v, (π (Exp v)).toAdd = q (heightProjection T.character v))

include q hExp π hπExp in
theorem heightProjection_conjugationDifferential
    (g : G) (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    heightProjection T.character (conjugationDifferentialHom (E := E) g v) =
      heightProjection T.character v := by
  apply q.injective
  rw [← hπExp, ← hπExp, ← conjugation_exponential hExp]
  simp only [map_mul, map_inv]
  simp

include q hExp π hπExp in
theorem conjugationDifferential_mem_heightKernel
    (g : G) {v : GroupLieAlgebra (𝓘(ℝ, E)) G} (hv : v ∈ T.kernelIdeal) :
    conjugationDifferentialHom (E := E) g v ∈ T.kernelIdeal := by
  apply (Submodule.Quotient.mk_eq_zero _).mp
  change heightProjection T.character (conjugationDifferentialHom (E := E) g v) = 0
  rw [heightProjection_conjugationDifferential T q hExp π hπExp]
  exact (Submodule.Quotient.mk_eq_zero _).mpr hv

end PolycyclicRecognition

end

end OAI
