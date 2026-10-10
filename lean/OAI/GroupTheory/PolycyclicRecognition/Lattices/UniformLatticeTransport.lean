import OAI.GroupTheory.PolycyclicRecognition.Lattices.UniformLatticeMetric

namespace OAI

/-! # Transporting a compact lattice cover through a group homeomorphism -/

noncomputable section
namespace PolycyclicRecognition
variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

omit [TopologicalSpace G] [TopologicalSpace H] in
def comapSubgroupEquiv (e : G ≃* H) (Λ : Subgroup H) :
    (Λ.comap e.toMonoidHom) ≃* Λ where
  toFun x := ⟨e x.val, x.property⟩
  invFun y := ⟨e.symm y.val, by change e (e.symm y.val) ∈ Λ; rw [e.apply_symm_apply]; exact y.property⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.val
  right_inv y := by apply Subtype.ext; exact e.apply_symm_apply y.val
  map_mul' x y := by apply Subtype.ext; exact e.map_mul x.val y.val

theorem IsUniformLattice.comap_mulEquiv (e : G ≃* H)
    (he : Continuous e) (hei : Continuous e.symm)
    {Λ : Subgroup H} (hΛ : IsUniformLattice Λ) :
    IsUniformLattice (Λ.comap e.toMonoidHom) := by
  let := hΛ.1
  let f : Λ.comap e.toMonoidHom → Λ := fun x => ⟨e x.val, x.property⟩
  have hf : Continuous f := (he.comp continuous_subtype_val).subtype_mk _
  have hdisc : DiscreteTopology (Λ.comap e.toMonoidHom) :=
    DiscreteTopology.of_continuous_injective hf (by
      intro x y h
      apply Subtype.ext
      exact e.injective (congrArg Subtype.val h))
  obtain ⟨K, hK, hc⟩ := hΛ.2
  refine ⟨hdisc, e.symm '' K, hK.image hei, ?_⟩
  intro g
  obtain ⟨a, k, hk, h⟩ := hc (e g)
  refine ⟨⟨e.symm a.val, by change e (e.symm a.val) ∈ Λ; rw [e.apply_symm_apply]; exact a.property⟩,
    e.symm k, ⟨k, hk, rfl⟩, ?_⟩
  change e.symm a.val * e.symm k = g
  rw [← map_mul, h, e.symm_apply_apply]

end PolycyclicRecognition

end

end OAI
