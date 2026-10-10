import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexWeightRange
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SolvableGroupLieAlgebra
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DiscreteLinearNilpotentKernel
import OAI.GroupTheory.PolycyclicRecognition.Lattices.TriangulableLatticePolycyclic

namespace OAI

/-! # Polycyclicity of lattices in simply connected solvable Lie groups

Complex adjoint weights include rotations. Their normalized additive lifts
have nilpotent Lie kernel and a real vector-space quotient. Discrete subgroups
of the kernel are polycyclic, and finite generation controls the abelian image.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

/-- Every finitely generated discrete subgroup of a connected simply
connected finite-dimensional real solvable Lie group is polycyclic. -/
theorem isPolycyclic_finitelyGenerated_discrete_solvableLieGroup
    {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]
    [SimplyConnectedSpace G] [Group.IsSolvable G]
    (Γ : Subgroup G) [DiscreteTopology Γ] [Group.FG Γ] : IsPolycyclic Γ := by
  let L := GroupLieAlgebra (𝓘(ℝ, E)) G
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let : LocallyPathConnectedSpace G := ChartedSpace.locallyPathConnectedSpace E G
  let : LieAlgebra.IsSolvable L := groupLieAlgebra_isSolvable (E := E) (G := G)
  obtain ⟨n, b, hb⟩ := exists_complex_triangular_adjoint_basis L
  let T : ComplexTriangularAdjoint L n := ⟨b, hb⟩
  let Exp := groupExponential (E := E) (G := G)
  have hExp : IsGroupExponential Exp := groupExponential_isGroupExponential
  obtain ⟨π, hπ, he⟩ := exists_additive_complex_adjoint_weights (Module.finBasis ℝ L) T hExp
  obtain ⟨q, hq, hqe⟩ := exists_range_restricted_complex_weights hExp T.weightMap π hπ he
  exact isPolycyclic_finitelyGenerated_discrete_of_linear_nilpotent_kernel
    T.kernelIdeal T.kernelIdeal_nilpotent T.weightMap.rangeRestrict
    T.weightMap.surjective_rangeRestrict (LinearMap.ker_rangeRestrict T.weightMap)
    Exp hExp q hq hqe Γ

/-- The full solvable lattice theorem used by the recognition argument. -/
theorem isPolycyclic_uniformLattice_solvableLieGroup
    (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier)
    (hΛ : IsUniformLattice Λ) : IsPolycyclic Λ := by
  obtain ⟨d⟩ := S.nonempty_properChainMetric geodesicMetricExistenceInput
  let := d.compatibleMetric
  let := d.proper_compatibleMetric
  let := d.isometric_compatibleMetric
  let : IsTopologicalGroup S.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, S.modelSpace)) ⊤
  let : DiscreteTopology Λ := hΛ.1
  let : Group.FG Λ := hΛ.finitelyGenerated d.chains_compatibleMetric
  exact isPolycyclic_finitelyGenerated_discrete_solvableLieGroup (E := S.modelSpace) Λ

end PolycyclicRecognition

end

end OAI
