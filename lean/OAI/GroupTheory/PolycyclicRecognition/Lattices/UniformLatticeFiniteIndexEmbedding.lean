import OAI.GroupTheory.PolycyclicRecognition.Lattices.UniformLatticeEmbedding

namespace OAI

/-! # Pulling a lattice back through a closed finite-index embedding -/

noncomputable section
namespace PolycyclicRecognition
open Set
variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

/-- If a closed subgroup contains the lattice, its induced lattice is uniform. -/
theorem IsUniformLattice.comap_of_le_range
    {Γ : Subgroup G} (hΓ : IsUniformLattice Γ) (f : H →* G)
    (hf : Topology.IsClosedEmbedding f) (hle : Γ ≤ f.range) :
    IsUniformLattice (Γ.comap f) := by
  let := hΓ.1
  let g : Γ.comap f → Γ := fun x => ⟨f x, x.property⟩
  have hg : Continuous g := (hf.continuous.comp continuous_subtype_val).subtype_mk _
  have hdisc : DiscreteTopology (Γ.comap f) :=
    DiscreteTopology.of_continuous_injective hg (by
      intro x y h
      exact Subtype.ext (hf.injective (congrArg Subtype.val h)))
  obtain ⟨K, hK, hcover⟩ := hΓ.2
  refine ⟨hdisc, f ⁻¹' K, hf.isCompact_preimage hK, ?_⟩
  intro x
  obtain ⟨γ, k, hk, he⟩ := hcover (f x)
  obtain ⟨a, ha⟩ := hle γ.property
  have haΓ : a ∈ Γ.comap f := by change f a ∈ Γ; rw [ha]; exact γ.property
  have hfk : f (a⁻¹ * x) = k := by
    rw [map_mul, map_inv, ha, ← he, inv_mul_cancel_left]
  refine ⟨⟨a, haΓ⟩, a⁻¹ * x, ?_, mul_inv_cancel_left a x⟩
  change f (a⁻¹ * x) ∈ K
  rw [hfk]
  exact hk

/-- Restriction to a closed finite-index subgroup preserves a uniform lattice. -/
theorem IsUniformLattice.comap_finiteIndex [IsTopologicalGroup G]
    {Γ : Subgroup G} (hΓ : IsUniformLattice Γ) (f : H →* G)
    (hf : Topology.IsClosedEmbedding f) [f.range.FiniteIndex] :
    IsUniformLattice (Γ.comap f) := by
  let J := f.range.comap Γ.subtype
  let : J.FiniteIndex := inferInstance
  have hJ := hΓ.finiteIndex J
  have hle : J.map Γ.subtype ≤ f.range := by
    rintro x ⟨y, hy, rfl⟩
    exact hy
  have heq : (J.map Γ.subtype).comap f = Γ.comap f := by
    ext x
    constructor
    · rintro ⟨y, _, hy⟩
      change f x ∈ Γ
      rw [← hy]
      exact y.property
    · intro hx
      exact ⟨⟨f x, hx⟩, ⟨x, rfl⟩, rfl⟩
  rw [← heq]
  exact hJ.comap_of_le_range f hf hle

end PolycyclicRecognition

end

end OAI
