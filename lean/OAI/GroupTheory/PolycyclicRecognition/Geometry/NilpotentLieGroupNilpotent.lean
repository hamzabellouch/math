import OAI.GroupTheory.PolycyclicRecognition.Geometry.DiscreteNilpotentLieGroup
import OAI.GroupTheory.PolycyclicRecognition.Algebra.UnipotentGroupNilpotent
import Mathlib.Topology.Metrizable.Uniformity

namespace OAI

/-! # Algebraic nilpotence of the simply connected nilpotent Lie models

The intrinsic height is zero when the tangent algebra is nilpotent. The
constructed faithful representation is therefore upper unipotent on the
whole group, and its finite matrix filtration proves group nilpotence.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

theorem nilpotent_group_of_nilpotent_lieAlgebra
    {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
    [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]
    [LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G)] : Group.IsNilpotent G := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  obtain ⟨a, ⟨T⟩⟩ := nonempty_triangularAdjoint_of_nilpotent
    (GroupLieAlgebra (𝓘(ℝ, E)) G)
  let W := Fin (Module.finrank ℝ (HeightSpace T.character)) → ℝ
  let q : HeightSpace T.character ≃ₗ[ℝ] W := (Module.finBasis ℝ _).equivFun
  let Exp := groupExponential (E := E) (G := G)
  have hExp : IsGroupExponential Exp := groupExponential_isGroupExponential
  obtain ⟨π, _, he, _⟩ := exists_intrinsic_canonical_height_with_kernel T q hExp
  have hπ : π = 1 := by
    apply monoidHom_ext_exponential hExp
    intro x
    apply Multiplicative.ext
    have hx : x ∈ T.kernelIdeal := T.mem_kernelIdeal_of_ad_nilpotent x
      (LieModule.isNilpotent_toEnd_of_isNilpotent ℝ _ _ x)
    have hz : heightProjection T.character x = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hx
    change (π (Exp x)).toAdd = 0
    rw [he, hz, map_zero]
  obtain ⟨m, ρ, hinj, _, hu⟩ :=
    exists_faithful_unipotent_representation_on_height_kernel T q Exp hExp π he
  exact nilpotent_of_faithful_strictUpper_representation ρ hinj
    (fun g => hu g (by change π g = 1; rw [hπ]; rfl))

theorem NilpotentLieModel.group_nilpotent
    {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
    (N : NilpotentLieModel L) (hn : LieRing.IsNilpotent L) : Group.IsNilpotent N.carrier := by
  obtain ⟨_, _, chart, _⟩ := N.exists_exponential_chart hn (nilpotentPublishedInputs.haar L N)
  let : TopologicalSpace.MetrizableSpace
      (GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier) :=
    (tangentSpaceCastModel (𝓘(ℝ, N.modelSpace)) (1 : N.carrier)).toHomeomorph.isEmbedding.metrizableSpace
  let : TopologicalSpace.MetrizableSpace N.carrier := chart.symm.isEmbedding.metrizableSpace
  let : MetricSpace N.carrier := TopologicalSpace.metrizableSpaceMetric N.carrier
  let : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier) :=
    N.tangent_nilpotent hn
  exact nilpotent_group_of_nilpotent_lieAlgebra (E := N.modelSpace) (G := N.carrier)

end PolycyclicRecognition

end

end OAI
