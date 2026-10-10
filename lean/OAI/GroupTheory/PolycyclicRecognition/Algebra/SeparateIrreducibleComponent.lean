import OAI.GroupTheory.PolycyclicRecognition.Algebra.SeparateGroupClosure
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SeparateFiniteIndexDensity
import Mathlib.Topology.Irreducible

namespace OAI

/-! # The irreducible identity component of a separately continuous group

Separate continuity suffices for products of irreducible sets. Consequently
the irreducible component of the identity is a normal subgroup, and it has
finite index in a Noetherian group.
-/

noncomputable section
namespace PolycyclicRecognition

open Set

theorem preirreducible_image2_of_separate_continuity
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {s : Set X} {t : Set Y} (hs : IsPreirreducible s) (ht : IsPreirreducible t)
    (f : X → Y → Z) (hx : ∀ y, Continuous (fun x => f x y))
    (hy : ∀ x, Continuous (f x)) : IsPreirreducible (Set.image2 f s t) := by
  intro U V hU hV hsu htv
  obtain ⟨_, ⟨x₀, hx₀, y₀, hy₀, rfl⟩, hu⟩ := hsu
  obtain ⟨_, ⟨x₁, hx₁, y₁, hy₁, rfl⟩, hv⟩ := htv
  obtain ⟨x, hxs, hxu, hxv⟩ := hs _ _ (hU.preimage (hx y₀))
    (hV.preimage (hx y₁)) ⟨x₀, hx₀, hu⟩ ⟨x₁, hx₁, hv⟩
  obtain ⟨y, hyt, hyu, hyv⟩ := ht _ _ (hU.preimage (hy x))
    (hV.preimage (hy x)) ⟨y₀, hy₀, hxu⟩ ⟨y₁, hy₁, hxv⟩
  exact ⟨f x y, ⟨x, hxs, y, hyt, rfl⟩, hyu, hyv⟩

variable {G : Type*} [Group G] [TopologicalSpace G]
  [SeparatelyContinuousMul G] [ContinuousInv G]

omit [ContinuousInv G] in
theorem preirreducible_subset_identityComponent {s : Set G}
    (hs : IsPreirreducible s) (h1 : (1 : G) ∈ s) :
    s ⊆ irreducibleComponent (1 : G) := by
  let C := irreducibleComponent (1 : G)
  have hm : IsPreirreducible (Set.image2 (· * ·) C s) :=
    preirreducible_image2_of_separate_continuity
      isIrreducible_irreducibleComponent.2 hs (· * ·)
      continuous_mul_const continuous_const_mul
  have hC : C ⊆ Set.image2 (· * ·) C s := by
    intro x hx
    exact ⟨x, hx, 1, h1, mul_one x⟩
  have he := eq_irreducibleComponent hm hC
  intro x hx
  rw [← he]
  exact ⟨1, mem_irreducibleComponent, x, hx, one_mul x⟩

def separateIrreducibleComponent (G : Type*) [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] [ContinuousInv G] : Subgroup G where
  carrier := irreducibleComponent (1 : G)
  one_mem' := mem_irreducibleComponent
  mul_mem' := by
    intro x y hx hy
    apply preirreducible_subset_identityComponent
      (preirreducible_image2_of_separate_continuity
        isIrreducible_irreducibleComponent.2 isIrreducible_irreducibleComponent.2
        (· * ·) continuous_mul_const continuous_const_mul)
    · exact ⟨1, mem_irreducibleComponent, 1, mem_irreducibleComponent, mul_one 1⟩
    · exact ⟨x, hx, y, hy, rfl⟩
  inv_mem' := by
    intro x hx
    apply preirreducible_subset_identityComponent
      (isIrreducible_irreducibleComponent.2.image (fun x : G => x⁻¹)
        continuous_inv.continuousOn)
    · exact ⟨1, mem_irreducibleComponent, inv_one⟩
    · exact ⟨x, hx, rfl⟩

instance separateIrreducibleComponent_normal : (separateIrreducibleComponent G).Normal where
  conj_mem x hx g := by
    apply preirreducible_subset_identityComponent
      (isIrreducible_irreducibleComponent.2.image (fun x : G => g * x * g⁻¹)
        ((continuous_const_mul g).mul_const g⁻¹).continuousOn)
    · exact ⟨1, mem_irreducibleComponent, by simp⟩
    · exact ⟨x, hx, rfl⟩

theorem separateIrreducibleComponent_closed :
    IsClosed (separateIrreducibleComponent G : Set G) := isClosed_irreducibleComponent

instance separateIrreducibleComponent_irreducible :
    IrreducibleSpace (separateIrreducibleComponent G) :=
  Subtype.irreducibleSpace isIrreducible_irreducibleComponent

theorem inverse_mul_mem_identityComponent_of_component_eq {x y : G}
    (h : irreducibleComponent x = irreducibleComponent y) :
    x⁻¹ * y ∈ separateIrreducibleComponent G := by
  apply preirreducible_subset_identityComponent
    (isIrreducible_irreducibleComponent.2.image (fun z : G => x⁻¹ * z)
      (continuous_const_mul x⁻¹).continuousOn)
  · exact ⟨x, mem_irreducibleComponent, inv_mul_cancel x⟩
  · refine ⟨y, ?_, rfl⟩
    rw [h]
    exact mem_irreducibleComponent

theorem separateIrreducibleComponent_finiteIndex [TopologicalSpace.NoetherianSpace G] :
    (separateIrreducibleComponent G).FiniteIndex := by
  classical
  let C := separateIrreducibleComponent G
  let : Finite (irreducibleComponents G) :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
  let f : G ⧸ C → irreducibleComponents G := fun q =>
    ⟨irreducibleComponent q.out, irreducibleComponent_mem_irreducibleComponents q.out⟩
  have hf : Function.Injective f := by
    intro a b hab
    have he : irreducibleComponent a.out = irreducibleComponent b.out :=
      congrArg Subtype.val hab
    have hm := inverse_mul_mem_identityComponent_of_component_eq he
    have hq : (a.out : G ⧸ C) = (b.out : G ⧸ C) := QuotientGroup.eq.mpr hm
    simpa only [Quotient.out_eq] using hq
  let : Finite (G ⧸ C) := Finite.of_injective f hf
  exact Subgroup.finiteIndex_of_finite_quotient

theorem noetherian_preconnected_group_irreducible
    [TopologicalSpace.NoetherianSpace G] [PreconnectedSpace G] : IrreducibleSpace G := by
  let C := separateIrreducibleComponent G
  let : C.FiniteIndex := separateIrreducibleComponent_finiteIndex
  have hclosed : IsClosed (C : Set G) := separateIrreducibleComponent_closed
  have hopen : IsOpen (C : Set G) := separate_isOpen_of_closed_finiteIndex C hclosed
  have he : (C : Set G) = Set.univ :=
    (show IsClopen (C : Set G) from ⟨hclosed, hopen⟩).eq_univ ⟨1, C.one_mem⟩
  exact {
    isPreirreducible_univ := he ▸ isIrreducible_irreducibleComponent.2
    toNonempty := inferInstance }

end PolycyclicRecognition

end

end OAI
