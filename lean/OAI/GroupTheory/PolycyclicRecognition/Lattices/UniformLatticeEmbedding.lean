import OAI.GroupTheory.PolycyclicRecognition.Lattices.UniformLatticeTransport
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.GroupTheory.Index

namespace OAI

/-! # Uniform lattices under cocompact embeddings and finite index -/

noncomputable section
namespace PolycyclicRecognition
open Set
open scoped Pointwise

variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

/-- A topological group embedding with a compact right fundamental cover
carries uniform lattices to uniform lattices. -/
theorem IsUniformLattice.map_of_compact_cover [IsTopologicalGroup H]
    {Λ : Subgroup G} (hΛ : IsUniformLattice Λ) (f : G →* H)
    (hf : Topology.IsEmbedding f) (K : Set H) (hK : IsCompact K)
    (hcover : ∀ h : H, ∃ (g : G) (k : H), k ∈ K ∧ f g * k = h) :
    IsUniformLattice (Λ.map f) := by
  let := hΛ.1
  have hi : Topology.IsEmbedding (fun a : Λ => f a) := hf.comp .subtypeVal
  have hr : Set.range (fun a : Λ => f a) = (Λ.map f : Set H) := by
    ext h
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hdisc : DiscreteTopology (Λ.map f) := by
    change DiscreteTopology (Λ.map f : Set H)
    rw [← hr]
    exact hi.toHomeomorph.symm.isEmbedding.discreteTopology
  obtain ⟨F, hF, hcovF⟩ := hΛ.2
  refine ⟨hdisc, (f '' F) * K, (hF.image hf.continuous).mul hK, ?_⟩
  intro h
  obtain ⟨g, k, hk, hg⟩ := hcover h
  obtain ⟨a, u, hu, ha⟩ := hcovF g
  refine ⟨⟨f a, ⟨a, a.property, rfl⟩⟩, f u * k, ⟨f u, ⟨u, hu, rfl⟩, k, hk, rfl⟩, ?_⟩
  change f a * (f u * k) = h
  rw [← mul_assoc, ← map_mul, ha, hg]

/-- A finite-index subgroup of a uniform lattice is again uniform in the
same ambient group. -/
theorem IsUniformLattice.finiteIndex [IsTopologicalGroup G]
    {Λ : Subgroup G} (hΛ : IsUniformLattice Λ) (J : Subgroup Λ) [J.FiniteIndex] :
    IsUniformLattice (J.map Λ.subtype) := by
  let := hΛ.1
  have hle : J.map Λ.subtype ≤ Λ := by
    rintro g ⟨a, _, rfl⟩
    exact a.property
  let f : J.map Λ.subtype → Λ := Subgroup.inclusion hle
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have hdisc : DiscreteTopology (J.map Λ.subtype) :=
    DiscreteTopology.of_continuous_injective hf (Subgroup.inclusion_injective hle)
  let R := Quotient (QuotientGroup.rightRel J)
  let : Finite R := Finite.of_equiv (Λ ⧸ J)
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel J).symm
  let reps : R → G := fun c => ((Quotient.out c : Λ) : G)
  obtain ⟨K, hK, hcover⟩ := hΛ.2
  refine ⟨hdisc, Set.range reps * K, (Set.finite_range reps).isCompact.mul hK, ?_⟩
  intro g
  obtain ⟨γ, k, hk, hγ⟩ := hcover g
  let c : R := Quotient.mk (QuotientGroup.rightRel J) γ
  let r : Λ := Quotient.out c
  have hj : γ * r⁻¹ ∈ J := QuotientGroup.rightRel_apply.mp
    (Quotient.exact' (Quotient.out_eq' c))
  refine ⟨⟨((γ * r⁻¹ : Λ) : G), ⟨γ * r⁻¹, hj, rfl⟩⟩, (r : G) * k,
    ⟨r, ⟨c, rfl⟩, k, hk, rfl⟩, ?_⟩
  change ((γ : G) * (r : G)⁻¹) * ((r : G) * k) = g
  rw [mul_assoc, inv_mul_cancel_left, hγ]

end PolycyclicRecognition

end

end OAI
