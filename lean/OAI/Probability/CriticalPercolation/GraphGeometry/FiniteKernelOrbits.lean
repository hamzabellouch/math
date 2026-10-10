import Mathlib

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.EquivariantCoordinates
variable {Λ N T V : Type*} [Group Λ] [Group N] [Group T] [MulAction Λ V]

theorem finite_orbit_of_finite_image (ρ : Λ →* N) (L : Subgroup Λ)
    (hfin : (L.map ρ : Set N).Finite)
    (hker : ∀ v : V, (MulAction.orbit ρ.ker v).Finite) (v : V) :
    (MulAction.orbit L v).Finite := by
  have hex : ∀ a : L.map ρ, ∃ g : Λ, g∈L ∧ ρ g=a := by
    intro a
    exact a.property
  choose r hr using hex
  let : Finite (L.map ρ) := hfin.to_subtype
  have hset : (⋃ a : L.map ρ, (fun x : V => r a • x) '' MulAction.orbit ρ.ker v).Finite :=
    Set.finite_iUnion (fun a => (hker v).image _)
  apply hset.subset
  rintro w ⟨g,hg⟩
  change (g : Λ) • v=w at hg
  let a : L.map ρ := ⟨ρ g,⟨g,g.property,rfl⟩⟩
  have hk : (r a)⁻¹*(g : Λ)∈ρ.ker := by
    change ρ ((r a)⁻¹*(g : Λ))=1
    rw [map_mul,map_inv,(hr a).2]
    exact inv_mul_cancel (ρ g)
  apply Set.mem_iUnion.mpr
  refine ⟨a,((r a)⁻¹*(g : Λ)) • v,?_,?_⟩
  · exact ⟨⟨(r a)⁻¹*(g : Λ),hk⟩,rfl⟩
  · change r a • (((r a)⁻¹*(g : Λ)) • v)=w
    rw [← mul_smul,mul_inv_cancel_left,hg]

lemma finite_composite_kernel_orbits (ρ : Λ →* N) (φ : N →* T)
    (hφ : (φ.ker : Set N).Finite)
    (hker : ∀ v : V, (MulAction.orbit ρ.ker v).Finite) (v : V) :
    (MulAction.orbit (φ.comp ρ).ker v).Finite := by
  apply finite_orbit_of_finite_image ρ _ _ hker v
  apply hφ.subset
  rintro n ⟨g,hg,rfl⟩
  exact hg

lemma finite_vertices_of_finite_quotient (ρ : Λ →* N) [Finite N]
    (hker : ∀ v : V, (MulAction.orbit ρ.ker v).Finite)
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s) :
    (Set.univ : Set V).Finite := by
  have hf : ∀ s : V, (MulAction.orbit Λ s).Finite := by
    intro s
    have hh := finite_orbit_of_finite_image ρ ⊤ (Set.toFinite _) hker s
    apply hh.subset
    rintro v ⟨g,hg⟩
    exact ⟨⟨g,Subgroup.mem_top g⟩,hg⟩
  apply (hS.biUnion fun s _ => hf s).subset
  intro v _
  obtain ⟨s,hs,hvs⟩ := hcover v
  exact Set.mem_iUnion₂.mpr ⟨s,hs,hvs⟩

end CriticalPercolation.EquivariantCoordinates
end
end
end

end OAI
