import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicTriangularTopology
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialRepresentationInput

namespace OAI

/-! # The complete triangular realization without a global exponential chart -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]

theorem onshuusPostRealizationInput_intrinsic
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a) :
    OnshuusPostRealizationInput T := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  intro Exp hExp
  obtain ⟨m, hm, j, ρ, hj, hu, hn, hρ, _, he⟩ :=
    exists_intrinsic_faithful_triangular_representation T Exp hExp
  have hind := intrinsic_triangular_representation_inducing T Exp hExp j hj hu ρ hρ he
  let S := (positiveTriangular m).comap ρ
  have hS : S = ⊤ := by
    apply subgroup_eq_top_of_exponential_basis hExp (Module.finBasis ℝ E)
    intro i t
    change ρ (Exp (t • Module.finBasis ℝ E i)) ∈ positiveTriangular m
    let v : GroupLieAlgebra (𝓘(ℝ, E)) G := t • Module.finBasis ℝ E i
    have hp : algebraExpUnit (j v) ∈ positiveTriangular m :=
      (positiveTriangularExp _ (hu v)).property
    exact (he v).symm ▸ hp
  have hpos (g : G) : ρ g ∈ positiveTriangular m := by
    change g ∈ S
    rw [hS]
    trivial
  let σ := ρ.codRestrict (positiveTriangular m) hpos
  refine ⟨m, hm, σ, hind, ?_⟩
  intro x hx
  change StrictUpper ((ρ (Exp x) : Matrix (Fin m) (Fin m) ℝ) - 1)
  rw [he, coe_algebraExpUnit]
  exact triangular_nilpotent_exp_unipotent (j x) (hu x) (hn x hx)

/-- The exponential-compatible inducing linear realization is constructed
from the actual Lie group, with no published realization premise. -/
theorem exponentialLinearRealizationInput_intrinsic :
    ExponentialLinearRealizationInput (EG := E) (G := G) := by
  rintro ⟨a, ⟨T⟩⟩ Exp hExp
  obtain ⟨m, hm, j, ρ, hj, hu, _, hρ, _, he⟩ :=
    exists_intrinsic_faithful_triangular_representation T Exp hExp
  exact ⟨m, hm, ρ, j,
    intrinsic_triangular_representation_inducing T Exp hExp j hj hu ρ hρ he, he⟩

end PolycyclicRecognition

end

end OAI
