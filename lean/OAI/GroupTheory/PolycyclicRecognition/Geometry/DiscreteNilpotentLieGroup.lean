import OAI.GroupTheory.PolycyclicRecognition.Geometry.DiscreteHeightKernel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SimultaneousAdjointBasis
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialHomExt

namespace OAI

/-! # Discrete subgroups of simply connected nilpotent Lie groups

Nilpotence makes every adjoint operator have only the zero generalized
weight. A simultaneous triangular basis therefore has zero height, and
the discrete height-kernel theorem applies to the whole group.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

/-- Engel nilpotence supplies the split adjoint basis needed by the concrete
height-kernel argument. -/
theorem nonempty_triangularAdjoint_of_nilpotent (L : Type*)
    [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L] [LieRing.IsNilpotent L] :
    ∃ n : ℕ, Nonempty (TriangularAdjoint L n) := by
  let : LieModule.IsTriangularizable ℝ L L :=
    { maxGenEigenspace_eq_top := fun x => by
        apply top_unique
        intro v _
        apply (le_iSup (fun r : ℝ => (LieModule.toEnd ℝ L L x).maxGenEigenspace r) 0)
        rw [Module.End.mem_maxGenEigenspace]
        obtain ⟨n, hn⟩ := LieModule.isNilpotent_toEnd_of_isNilpotent ℝ L L x
        refine ⟨n, ?_⟩
        simpa using congrArg (fun f : Module.End ℝ L => f v) hn }
  exact nonempty_triangularAdjoint_of_split L

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]

/-- Every discrete subgroup is polycyclic; finite generation is a conclusion. -/
theorem isPolycyclic_discrete_nilpotent_lieGroup
    [LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, E)) G)]
    (Γ : Subgroup G) [DiscreteTopology Γ] : IsPolycyclic Γ := by
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
  apply isPolycyclic_discrete_height_kernel T q Exp hExp π he Γ
  intro g _
  change π g = 1
  rw [hπ]
  rfl

end PolycyclicRecognition

end

end OAI
