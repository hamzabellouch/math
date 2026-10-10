import OAI.GroupTheory.PolycyclicRecognition.Geometry.SemidirectProductTopology
import OAI.GroupTheory.PolycyclicRecognition.Lattices.UniformLatticeMetric

namespace OAI

/-! # Uniform lattices in a semidirect product

The lattices in the two factors form a lattice whenever the acting lattice
preserves the first lattice. The compact cover uses the inverse action before
reducing the first coordinate.
-/

noncomputable section
namespace PolycyclicRecognition
open Set
variable {N D : Type*} [Group N] [Group D]
  [TopologicalSpace N] [TopologicalSpace D]
  (φ : D →* MulAut N) (Λ : Subgroup N) (Δ : Subgroup D)
  (hφ : ∀ d ∈ Δ, ∀ x ∈ Λ, φ d x ∈ Λ)

attribute [local instance] semidirectProductTopology

def semidirectLattice : Subgroup (N ⋊[φ] D) where
  carrier := {p | p.left ∈ Λ ∧ p.right ∈ Δ}
  one_mem' := ⟨Λ.one_mem, Δ.one_mem⟩
  mul_mem' := by
    intro p q hp hq
    exact ⟨Λ.mul_mem hp.1 (hφ p.right hp.2 q.left hq.1), Δ.mul_mem hp.2 hq.2⟩
  inv_mem' := by
    intro p hp
    exact ⟨hφ p.right⁻¹ (Δ.inv_mem hp.2) p.left⁻¹ (Λ.inv_mem hp.1), Δ.inv_mem hp.2⟩

theorem semidirectLattice_discrete [DiscreteTopology Λ] [DiscreteTopology Δ] :
    DiscreteTopology (semidirectLattice φ Λ Δ hφ) := by
  let f : semidirectLattice φ Λ Δ hφ → Λ × Δ :=
    fun x => (⟨x.val.left, x.property.1⟩, ⟨x.val.right, x.property.2⟩)
  have hl := (continuous_semidirect_left φ).comp
    (continuous_subtype_val : Continuous (Subtype.val : semidirectLattice φ Λ Δ hφ → N ⋊[φ] D))
  have hr := (continuous_semidirect_right φ).comp
    (continuous_subtype_val : Continuous (Subtype.val : semidirectLattice φ Λ Δ hφ → N ⋊[φ] D))
  have hf : Continuous f := (hl.subtype_mk _).prodMk (hr.subtype_mk _)
  apply DiscreteTopology.of_continuous_injective hf
  intro x y h
  apply Subtype.ext
  apply SemidirectProduct.ext
  · exact congrArg (fun z : Λ × Δ => z.1.val) h
  · exact congrArg (fun z : Λ × Δ => z.2.val) h

theorem semidirectLattice_uniform (hΛ : IsUniformLattice Λ) (hΔ : IsUniformLattice Δ) :
    IsUniformLattice (semidirectLattice φ Λ Δ hφ) := by
  let := hΛ.1
  let := hΔ.1
  obtain ⟨K, hK, hcoverK⟩ := hΛ.2
  obtain ⟨F, hF, hcoverF⟩ := hΔ.2
  let e := semidirectProductHomeomorph φ
  refine ⟨semidirectLattice_discrete φ Λ Δ hφ,
    e.symm '' (K ×ˢ F), (hK.prod hF).image e.symm.continuous, ?_⟩
  intro g
  obtain ⟨δ, v, hv, hδ⟩ := hcoverF g.right
  obtain ⟨μ, u, hu, hμ⟩ := hcoverK (φ (δ.val⁻¹) g.left)
  let γ : semidirectLattice φ Λ Δ hφ :=
    ⟨⟨φ δ.val μ.val, δ.val⟩, hφ δ.val δ.property μ.val μ.property, δ.property⟩
  refine ⟨γ, ⟨u, v⟩, ⟨(u, v), ⟨hu, hv⟩, rfl⟩, ?_⟩
  apply SemidirectProduct.ext
  · change φ δ.val μ.val * φ δ.val u = g.left
    rw [← map_mul, hμ, map_inv]
    exact (φ δ.val).apply_symm_apply g.left
  · exact hδ

end PolycyclicRecognition

end

end OAI
