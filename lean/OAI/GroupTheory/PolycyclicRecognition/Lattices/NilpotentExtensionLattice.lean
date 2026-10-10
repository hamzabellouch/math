import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentExtensionEmbedding
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorExtensionTopology

namespace OAI

/-! # A uniform lattice after completing only the nilpotent kernel

The quotient is still discrete. This is an intermediate construction, not a
claim that the resulting group is connected.
-/

noncomputable section
namespace PolycyclicRecognition.NilpotentLatticeCoordinates
open Set
open scoped Manifold
variable {N G Q : Type} [Group N] [Group G] [Group Q]
  [TopologicalSpace Q] [DiscreteTopology Q]
  (C : NilpotentLatticeCoordinates N) (S : GroupExtension N G Q)
  (σ : S.Section) (hσ : σ 1 = 1)
attribute [local instance] factorExtensionTopology

def completedExtensionLattice : Subgroup (FactorExtension (C.extensionFactorSystem S σ hσ)) :=
  (C.extensionEmbedding S σ hσ).range

theorem completedExtensionLattice_discrete :
    DiscreteTopology (C.completedExtensionLattice S σ hσ) := by
  let := C.uniform.1
  let f : C.completedExtensionLattice S σ hσ → C.lattice × Q := fun a =>
    (⟨a.val.left, (C.mem_extensionEmbedding_range S σ hσ a.val).mp a.property⟩, a.val.right)
  have hl := (continuous_factor_left (C.extensionFactorSystem S σ hσ)).comp
    (continuous_subtype_val : Continuous (Subtype.val : C.completedExtensionLattice S σ hσ → _))
  have hr := (continuous_factor_right (C.extensionFactorSystem S σ hσ)).comp
    (continuous_subtype_val : Continuous (Subtype.val : C.completedExtensionLattice S σ hσ → _))
  have hf : Continuous f := (hl.subtype_mk _).prodMk hr
  apply DiscreteTopology.of_continuous_injective hf
  intro a b h
  apply Subtype.ext
  apply FactorExtension.ext
  · exact congrArg (fun z : C.lattice × Q => (z.1 : C.carrier)) h
  · exact congrArg (fun z : C.lattice × Q => z.2) h

omit [TopologicalSpace Q] [DiscreteTopology Q] in
theorem extension_action_lattice (q : Q) (x : C.lattice) :
    (C.extensionFactorSystem S σ hσ).action q x ∈ C.lattice := by
  obtain ⟨n, hn⟩ := C.equiv.surjective x
  rw [← hn]
  change C.automorphism (S.conjAct (σ q)) (C.equiv n) ∈ C.lattice
  rw [C.automorphism_on_lattice]
  exact (C.equiv _).property

/-- Compactness of the original kernel fundamental cover is retained by the
completed extension, even though its quotient may be infinite and nonsplit. -/
theorem completedExtensionLattice_uniform :
    IsUniformLattice (C.completedExtensionLattice S σ hσ) := by
  let T := C.extensionFactorSystem S σ hσ
  obtain ⟨K, hK, hcover⟩ := C.uniform.2
  refine ⟨C.completedExtensionLattice_discrete S σ hσ,
    FactorExtension.inl T '' K, hK.image (continuous_factor_inl T), ?_⟩
  intro g
  obtain ⟨μ, u, hu, heq⟩ := hcover ((T.action g.right).symm g.left)
  let γ : C.completedExtensionLattice S σ hσ :=
    ⟨⟨T.action g.right μ, g.right⟩,
      (C.mem_extensionEmbedding_range S σ hσ _).mpr
        (C.extension_action_lattice S σ hσ g.right μ)⟩
  refine ⟨γ, FactorExtension.inl T u, ⟨u, hu, rfl⟩, ?_⟩
  apply FactorExtension.ext
  · change T.action g.right μ * T.action g.right u * T.factor g.right 1 = g.left
    rw [T.factor_one_right, mul_one, ← map_mul, heq]
    exact (T.action g.right).apply_symm_apply g.left
  · exact mul_one g.right

/-- The lattice is isomorphic to the original group, not a quotient by its center. -/
def completedExtensionLatticeEquiv : G ≃* C.completedExtensionLattice S σ hσ :=
  MonoidHom.ofInjective (C.extensionEmbedding_injective S σ hσ)

theorem completedExtension_topologicalGroup :
    IsTopologicalGroup (FactorExtension (C.extensionFactorSystem S σ hσ)) := by
  let : IsTopologicalGroup C.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, C.carrier)) ⊤
  exact factorExtensionTopologicalGroup _
    (fun q => (C.extensionFactorSystem_smooth S σ hσ q).continuous)

end PolycyclicRecognition.NilpotentLatticeCoordinates

end

end OAI
