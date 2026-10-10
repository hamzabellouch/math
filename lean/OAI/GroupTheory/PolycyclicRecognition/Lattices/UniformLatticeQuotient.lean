import OAI.GroupTheory.PolycyclicRecognition.Lattices.UniformLatticeMetric
import Mathlib.Topology.Algebra.Group.Quotient

namespace OAI

/-! # Compact quotient and compact fundamental cover

The concrete uniform lattice definition agrees with the usual compact-coset-
quotient definition. Left and right cosets are interchanged by inversion.
-/

noncomputable section

namespace PolycyclicRecognition

open Set
open scoped Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The compact fundamental cover gives compactness of the ordinary right
coset quotient, without any normality assumption. -/
theorem IsUniformLattice.compactSpace_quotient {Λ : Subgroup G}
    (hΛ : IsUniformLattice Λ) : CompactSpace (G ⧸ Λ) := by
  obtain ⟨K, hK, hcover⟩ := hΛ.2
  let q : G → G ⧸ Λ := QuotientGroup.mk
  have hsurj : (fun k => q k⁻¹) '' K = univ := by
    apply eq_univ_of_forall
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨γ, k, hk, heq⟩ := hcover a⁻¹
    refine ⟨k, hk, ?_⟩
    apply QuotientGroup.eq.mpr
    simp only [inv_inv]
    have hka : k * a = (γ : G)⁻¹ := by
      calc
        k * a = (γ : G)⁻¹ * ((γ : G) * k) * a := by group
        _ = (γ : G)⁻¹ := by rw [heq]; group
    rw [hka]
    exact Λ.inv_mem γ.property
  apply isCompact_univ_iff.mp
  rw [← hsurj]
  exact hK.image (QuotientGroup.continuous_mk.comp continuous_inv)

/-- In a locally compact group, a compact coset quotient admits a compact
fundamental cover. The finite subcover consists of images of relatively
compact neighborhoods. -/
theorem isUniformLattice_of_compact_quotient [LocallyCompactSpace G]
    (Λ : Subgroup G) [DiscreteTopology Λ] [CompactSpace (G ⧸ Λ)] :
    IsUniformLattice Λ := by
  let q : G → G ⧸ Λ := QuotientGroup.mk
  choose K hK hneigh using fun x : G => exists_compact_mem_nhds x
  have hxK (x : G) : x ∈ interior (K x) := mem_interior_iff_mem_nhds.mpr (hneigh x)
  have hcover : (univ : Set (G ⧸ Λ)) ⊆ ⋃ x : G, q '' interior (K x) := by
    intro y _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact mem_iUnion.mpr ⟨x, ⟨x, hxK x, rfl⟩⟩
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun x : G => q '' interior (K x))
    (fun x => QuotientGroup.isOpenMap_coe _ isOpen_interior) hcover
  let L : Set G := ⋃ x ∈ F, K x
  have hL : IsCompact L := F.isCompact_biUnion (fun x _ => hK x)
  refine ⟨inferInstance, Inv.inv '' L, hL.image continuous_inv, ?_⟩
  intro g
  obtain ⟨x, hx, k, hk, hkg⟩ := mem_iUnion₂.mp (hF (mem_univ (q g⁻¹)))
  have hrel : k⁻¹ * g⁻¹ ∈ Λ := QuotientGroup.eq.mp hkg
  refine ⟨⟨g * k, ?_⟩, k⁻¹, ⟨k, ?_, rfl⟩, ?_⟩
  · simpa only [mul_inv_rev, inv_inv] using Λ.inv_mem hrel
  · exact mem_iUnion₂.mpr ⟨x, hx, interior_subset hk⟩
  · simp [mul_assoc]

/-- This is the usual uniform-lattice predicate in locally compact groups. -/
theorem isUniformLattice_iff_compact_quotient [LocallyCompactSpace G] (Λ : Subgroup G) :
    IsUniformLattice Λ ↔ DiscreteTopology Λ ∧ CompactSpace (G ⧸ Λ) := by
  constructor
  · intro h
    exact ⟨h.1, h.compactSpace_quotient⟩
  · rintro ⟨hdisc, hcompact⟩
    let := hdisc
    let := hcompact
    exact isUniformLattice_of_compact_quotient Λ

end PolycyclicRecognition

end

end OAI
