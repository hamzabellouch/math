import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolyZFiniteIndex

namespace OAI

/-! # The virtual poly-Z refinement of a polycyclic series -/

noncomputable section
namespace PolycyclicRecognition

open ChromaticCyclic
variable {G J : Type} [Group G] [Group J]

theorem polyZ_finiteIndex_of_equiv (e : G ≃* J)
    (h : ∃ H : Subgroup G, H.FiniteIndex ∧ IsPolyZ H) :
    ∃ K : Subgroup J, K.FiniteIndex ∧ IsPolyZ K := by
  obtain ⟨H, hHi, hHz⟩ := h
  let := hHi
  let d := H.equivMapOfInjective e.toMonoidHom e.injective
  exact ⟨H.map e.toMonoidHom, Subgroup.FiniteIndex.map_of_surjective H e.surjective,
    hHz.of_equiv d⟩

theorem polyZ_finiteIndex_of_cyclicStep {H K : Subgroup G}
    (s : CyclicStep H K) (hfg : Group.FG H)
    (hH : ∃ L : Subgroup H, L.FiniteIndex ∧ IsPolyZ L) :
    ∃ L : Subgroup K, L.FiniteIndex ∧ IsPolyZ L := by
  let e := (Subgroup.subgroupOfEquivOfLe s.le).symm
  let : Group.FG (H.subgroupOf K) :=
    @Group.fg_of_surjective _ _ _ _ hfg e.toMonoidHom e.surjective
  let := s.normal
  let := s.cyclic
  exact polyZ_finiteIndex_of_cyclic_extension (H.subgroupOf K)
    (polyZ_finiteIndex_of_equiv e hH)

theorem IsPolycyclic.exists_polyZ_finiteIndex (hG : IsPolycyclic G) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ IsPolyZ H := by
  obtain ⟨n, ⟨c⟩⟩ := hG
  have hm : ∀ i, i ≤ n → Group.FG (c.group i) ∧
      ∃ H : Subgroup (c.group i), H.FiniteIndex ∧ IsPolyZ H := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [c.first]
      exact ⟨inferInstance, ⊤, inferInstance, isPolyZ_of_subsingleton⟩
    | succ i ih =>
      intro hi
      obtain ⟨hfg, hz⟩ := ih (by omega)
      exact ⟨finitelyGenerated_of_cyclicStep (c.step i (by omega)) hfg,
        polyZ_finiteIndex_of_cyclicStep (c.step i (by omega)) hfg hz⟩
  have htop := (hm n le_rfl).2
  rw [c.last] at htop
  exact polyZ_finiteIndex_of_equiv Subgroup.topEquiv htop

end PolycyclicRecognition

end

end OAI
