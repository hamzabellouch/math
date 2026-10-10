import OAI.GroupTheory.PolycyclicRecognition.Algebra.DiscreteUnipotentGroup
import OAI.GroupTheory.PolycyclicRecognition.Analysis.IntrinsicKernelPacking

namespace OAI

/-! # Discrete subgroups of the intrinsic height kernel

The actual closed nilpotent kernel supplies exponential preimages. The
intrinsic faithful triangular representation is upper unipotent on those
preimages, so its discrete subgroups are polycyclic.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- One faithful inducing representation is unipotent on every element of
the actual height kernel. -/
theorem exists_faithful_unipotent_representation_on_height_kernel
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (q : HeightSpace T.character ≃ₗ[ℝ] W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (π : G →* Multiplicative W)
    (he : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x)) :
    ∃ m : ℕ, ∃ ρ : G →* (Matrix (Fin m) (Fin m) ℝ)ˣ,
      Function.Injective ρ ∧
      Topology.IsInducing (fun g => (ρ g : Matrix (Fin m) (Fin m) ℝ)) ∧
      ∀ g ∈ π.ker, StrictUpper ((ρ g : Matrix (Fin m) (Fin m) ℝ) - 1) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  let d := q.toLinearMap.comp (heightProjection T.character)
  have hπ : Continuous π := (contMDiff_height_of_exponential_linear hExp π d he).continuous
  obtain ⟨N, ExpN, hExpN, ι, _, _, hιExp, hrange⟩ :=
    exists_closed_intrinsic_height_kernel T q Exp hExp π hπ he
  obtain ⟨cN, hcN⟩ := ((nilpotentPublishedInputs.haar T.kernelIdeal N).2 ExpN hExpN
    (N.tangent_nilpotent T.kernelIdeal_nilpotent)).1
  obtain ⟨m, _, j, ρ, hj, hu, hn, hρ, hinj, hρExp⟩ :=
    exists_intrinsic_faithful_triangular_representation T Exp hExp
  have hind := intrinsic_triangular_representation_inducing T Exp hExp j hj hu ρ hρ hρExp
  refine ⟨m, ρ, hinj, hind, ?_⟩
  intro g hg
  have hgrange : g ∈ Set.range ι := by
    rw [hrange]
    exact hg
  obtain ⟨n, hn'⟩ := hgrange
  obtain ⟨v, hv⟩ := cN.surjective n
  have hx : Exp (N.equiv.symm v) = g := by
    rw [← hιExp]
    simp only [N.equiv.apply_symm_apply]
    rw [← hcN, hv, hn']
  rw [← hx, hρExp, coe_algebraExpUnit]
  exact triangular_nilpotent_exp_unipotent _ (hu _) (hn _ (N.equiv.symm v).property)

/-- A discrete subgroup of the height kernel is polycyclic, without an
initial finite-generation assumption. -/
theorem isPolycyclic_discrete_height_kernel
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (q : HeightSpace T.character ≃ₗ[ℝ] W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (π : G →* Multiplicative W)
    (he : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x))
    (Γ : Subgroup G) [DiscreteTopology Γ] (hΓ : Γ ≤ π.ker) : IsPolycyclic Γ := by
  obtain ⟨m, ρ, hinj, hind, hu⟩ :=
    exists_faithful_unipotent_representation_on_height_kernel T q Exp hExp π he
  exact isPolycyclic_of_discrete_strictUpper_representation (ρ.comp Γ.subtype)
    (hind.comp Topology.IsInducing.subtypeVal) (hinj.comp Subtype.val_injective)
    (fun g => hu g (hΓ g.property))

/-- The ambient discrete group is a polycyclic extension of its intersection
with the height kernel by its finitely generated abelian height image. -/
theorem isPolycyclic_finitelyGenerated_discrete_height_extension
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (q : HeightSpace T.character ≃ₗ[ℝ] W)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (π : G →* Multiplicative W)
    (he : ∀ x, (π (Exp x)).toAdd = q (heightProjection T.character x))
    (Γ : Subgroup G) [DiscreteTopology Γ] [Group.FG Γ] : IsPolycyclic Γ := by
  obtain ⟨m, ρ, hinj, hind, hu⟩ :=
    exists_faithful_unipotent_representation_on_height_kernel T q Exp hExp π he
  let f := π.comp Γ.subtype
  let j := Γ.subtype.comp f.ker.subtype
  have hj : Function.Injective j := Subtype.val_injective.comp Subtype.val_injective
  have hjtop : Topology.IsInducing j :=
    Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  have hker : IsPolycyclic f.ker :=
    isPolycyclic_of_discrete_strictUpper_representation (ρ.comp j)
      (hind.comp hjtop) (hinj.comp hj) (fun g => hu (j g) g.property)
  have hQ : IsPolycyclic (Γ ⧸ f.ker) :=
    (isPolycyclic_equiv (QuotientGroup.quotientKerEquivRange f)).mpr
      (isPolycyclic_of_finitelyGenerated_commGroup f.range)
  exact isPolycyclic_of_normal_subgroup f.ker hker hQ

/-- The needed lattice-polycyclicity specialization for an ambient group
whose actual adjoint Lie representation is real triangular. -/
theorem isPolycyclic_finitelyGenerated_discrete_of_triangularAdjoint
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, E)) G) a)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (Γ : Subgroup G) [DiscreteTopology Γ] [Group.FG Γ] : IsPolycyclic Γ := by
  let W := Fin (Module.finrank ℝ (HeightSpace T.character)) → ℝ
  let q : HeightSpace T.character ≃ₗ[ℝ] W := (Module.finBasis ℝ _).equivFun
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ⊤
  obtain ⟨π, _, he, _⟩ := exists_intrinsic_canonical_height_with_kernel T q hExp
  exact isPolycyclic_finitelyGenerated_discrete_height_extension T q Exp hExp π he Γ

end PolycyclicRecognition

end

end OAI
