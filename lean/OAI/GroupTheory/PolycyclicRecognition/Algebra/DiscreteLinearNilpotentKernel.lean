import OAI.GroupTheory.PolycyclicRecognition.Geometry.DiscreteNilpotentLieGroup
import OAI.GroupTheory.PolycyclicRecognition.Algebra.LinearNilpotentKernel

namespace OAI

/-! # Lattice finiteness from a nilpotent linear kernel

The quotient may include lifted rotational characters. Discrete subgroups of
its kernel lift to the constructed simply connected nilpotent Lie model.
For a finitely generated ambient discrete subgroup the remaining quotient
is finitely generated abelian, giving polycyclicity.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- No finite-generation premise is needed for a discrete subgroup of the
constructed nilpotent kernel. -/
theorem isPolycyclic_discrete_linear_nilpotent_kernel
    (I : LieIdeal ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) (hI : LieRing.IsNilpotent I)
    (d : E →ₗ[ℝ] W) (hd : Function.Surjective d)
    (hker : LinearMap.ker d = I.toSubmodule)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (π : G →* Multiplicative W) (hπ : Continuous π)
    (he : ∀ x, (π (Exp x)).toAdd = d x)
    (Γ : Subgroup G) [DiscreteTopology Γ] (hΓ : Γ ≤ π.ker) : IsPolycyclic Γ := by
  obtain ⟨N, ExpN, _, ι, hι, _, _, hrange⟩ :=
    exists_closed_linear_nilpotent_kernel I hI d hd hker Exp hExp π hπ he
  let : MetricSpace N.carrier := hι.isEmbedding.comapMetricSpace ι
  let A := Γ.comap ι
  let : DiscreteTopology A := DiscreteTopology.preimage_of_continuous_injective
    (Γ : Set G) hι.continuous hι.injective
  let : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier) :=
    N.tangent_nilpotent hI
  have hA := isPolycyclic_discrete_nilpotent_lieGroup (E := N.modelSpace) A
  let f : A →* Γ := (ι.comp A.subtype).codRestrict Γ (fun a => a.property)
  apply hA.of_surjective f
  intro g
  have hg : (g : G) ∈ Set.range ι := by
    rw [hrange]
    exact hΓ g.property
  obtain ⟨n, hn⟩ := hg
  exact ⟨⟨n, by change ι n ∈ Γ; rw [hn]; exact g.property⟩, Subtype.ext hn⟩

/-- A finitely generated discrete subgroup is polycyclic whenever the
ambient additive quotient has nilpotent Lie kernel. -/
theorem isPolycyclic_finitelyGenerated_discrete_of_linear_nilpotent_kernel
    (I : LieIdeal ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)) (hI : LieRing.IsNilpotent I)
    (d : E →ₗ[ℝ] W) (hd : Function.Surjective d)
    (hker : LinearMap.ker d = I.toSubmodule)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (π : G →* Multiplicative W) (hπ : Continuous π)
    (he : ∀ x, (π (Exp x)).toAdd = d x)
    (Γ : Subgroup G) [DiscreteTopology Γ] [Group.FG Γ] : IsPolycyclic Γ := by
  let f := π.comp Γ.subtype
  let K := f.ker.map Γ.subtype
  have hKΓ : (K : Set G) ⊆ (Γ : Set G) := by
    rintro g ⟨x, _, rfl⟩
    exact x.property
  let : DiscreteTopology K := DiscreteTopology.of_subset (inferInstance : DiscreteTopology Γ) hKΓ
  have hKker : K ≤ π.ker := by
    rintro g ⟨x, hx, rfl⟩
    exact hx
  have hK := isPolycyclic_discrete_linear_nilpotent_kernel
    I hI d hd hker Exp hExp π hπ he K hKker
  let e := f.ker.equivMapOfInjective Γ.subtype Subtype.val_injective
  have hF : IsPolycyclic f.ker := hK.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hQ : IsPolycyclic (Γ ⧸ f.ker) :=
    (isPolycyclic_equiv (QuotientGroup.quotientKerEquivRange f)).mpr
      (isPolycyclic_of_finitelyGenerated_commGroup f.range)
  exact isPolycyclic_of_normal_subgroup f.ker hF hQ

end PolycyclicRecognition

end

end OAI
